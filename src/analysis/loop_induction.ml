open Ast
open Format
open Range
open Util
open Stdlib

(* -------------------------------------------------- *)
(* Mode flags *)
(* -------------------------------------------------- *)

let infer  = ref false
let verify = ref false

let set_mode mode =
  match mode with
  | "infer"  -> infer := true
  | "verify" -> verify := true
  | _ -> ()

(* -------------------------------------------------- *)
(* Expression helpers *)
(* -------------------------------------------------- *)

let true_exp  : exp node   = no_loc (CBool true)
let empty_blk : block node = no_loc []

let mk_id x    = no_loc (Id x)
let mk_int n   = no_loc (CInt (Int64.of_int n))

let mk_bin op a b = no_loc (Bop (op, a, b))
let mk_un  op a   = no_loc (Uop (op, a))

let mk_and  a b = mk_bin And a b
let mk_or   a b = mk_bin Or a b
let mk_add  a b = mk_bin Add a b
let mk_sub  a b = mk_bin Sub a b
let mk_eq   a b = mk_bin Eq a b
let mk_lte  a b = mk_bin Lte a b

let mk_not a = mk_un Lognot a

let mk_implies j phi =
  mk_or (mk_not j) phi

(* -------------------------------------------------- *)
(* Invariant setup *)
(* -------------------------------------------------- *)

(* base = c_init + (x - x_init) *)
let base =
  mk_add (mk_id "c_init")
         (mk_sub (mk_id "x") (mk_id "x_init"))

(* I = c <= base *)
let exp_I =
  mk_lte (mk_id "c") base

let exp_J = exp_I

(* φ′ = c > 0 *)
let exp_phi' =
  mk_bin Gt (mk_id "c") (no_loc (CInt 0L))

let implies_exp =
  mk_implies exp_J exp_phi'

(* -------------------------------------------------- *)
(* Loop extraction *)
(* -------------------------------------------------- *)

let block_has_loop (b : block node) =
  List.exists
    (fun s ->
      match s.elt with
      | While _ -> true
      | _ -> false)
    b.elt

let extract_loop_body (b : block node) =
  match b.elt with
  | [ { elt = While (cond, body); _ } ] ->
      (cond, body)
  | _ ->
      failwith "Expected a single While loop block"

let split_S_C1 blocks =
  match List.partition block_has_loop blocks with
  | [s_blk], [c1_blk] ->
      let (cond, body) = extract_loop_body s_blk in
      (cond, body, c1_blk)

  | _ ->
      failwith "Expected exactly one loop-containing block"

(* -------------------------------------------------- *)
(* Commute premise generation *)
(* -------------------------------------------------- *)

let mk_commute cv cc b1 b2 pre post loc =
  { elt = Commute (cv, cc, [b1; b2], pre, post); loc }

let choose_cond default phi =
  if !verify then PhiExp phi else default

let commute_premises cv cc blocks loc =
  let (loop_cond, block_S, block_C1) =
    split_S_C1 blocks
  in

  let cond_true = choose_cond cc true_exp in
  let cond_phi  = choose_cond cc exp_phi' in

  let premise1 =
    mk_commute cv cond_true
      empty_blk block_S
      (Some (mk_and exp_J loop_cond))
      (Some exp_J)
      loc
  in

  let premise2 =
    no_loc (Assert implies_exp)
  in

  let premise3 =
    mk_commute cv cond_phi
      block_C1 block_S
      None None
      loc
  in

  let premise4 =
    mk_commute cv cond_true
      block_C1 empty_blk
      (Some exp_I)
      (Some exp_I)
      loc
  in

  let premise5 =
    let nb = mk_not loop_cond in
    mk_commute cv cond_true
      block_C1 empty_blk
      (Some nb)
      (Some nb)
      loc
  in

  [ premise1; premise2; premise3; premise4; premise5 ]

(* -------------------------------------------------- *)
(* Rewrite commute statements *)
(* -------------------------------------------------- *)

let rewrite_commute_stmt (s : stmt node) =
  match s.elt with
  | Commute (cv, cc, blocks, _, _) ->
      commute_premises cv cc blocks s.loc
  | _ ->
      [s]

(* -------------------------------------------------- *)
(* Rewrite blocks + statements *)
(* -------------------------------------------------- *)

let rec rewrite_block (b : block node) =
  node_app
    (fun stmts ->
      stmts
      |> List.map rewrite_stmt
      |> List.flatten)
    b

and rewrite_stmt (s : stmt node) =
  match s.elt with
  | If (e, b1, b2) ->
      [ node_up s (If (e, rewrite_block b1, rewrite_block b2)) ]

  | While (e, b) ->
      [ node_up s (While (e, rewrite_block b)) ]

  | For (i, c, st, b) ->
      [ node_up s (For (i, c, st, rewrite_block b)) ]

  | SBlock (lbl, b) ->
      [ node_up s (SBlock (lbl, rewrite_block b)) ]

  | Commute _ ->
      rewrite_commute_stmt s

  | _ ->
      [s]

(* -------------------------------------------------- *)
(* Rewrite methods + program *)
(* -------------------------------------------------- *)

let rewrite_method (m : mdecl node) =
  node_app
    (fun m ->
      { m with
        body =
          node_app
            (fun stmts ->
              stmts
              |> List.map rewrite_stmt
              |> List.flatten)
            m.body
      })
    m

let rewrite_decl = function
  | Gmdecl m -> Gmdecl (rewrite_method m)
  | other -> other

let rewrite_program (p : prog) mode =
  set_mode mode;
  List.map rewrite_decl p

(** TODO: check if we have the pattern C1 and loop; for now assume*)