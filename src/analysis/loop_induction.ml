open Ast
open Format
open Range
open Util
open Stdlib
open Ast_print

(* -------------------------------------------------- *)
(* Mode flags *)
(* -------------------------------------------------- *)

let infer  = ref false
let verify = ref false

let set_mode = function
  | "infer"  -> infer := true
  | "verify" -> verify := true
  | _ -> ()

(* -------------------------------------------------- *)
(* Expression helpers *)
(* -------------------------------------------------- *)

let true_exp  : exp node   = no_loc (CBool true)
let empty_blk : block node = no_loc []
let zero      : exp node   = no_loc (CInt 0L)

let mk_id x = no_loc (Id x)
let mk_int n   = no_loc (CInt (Int64.of_int n))

let mk_bin op a b = no_loc (Bop (op, a, b))
let mk_un  op a   = no_loc (Uop (op, a))

let mk_and a b = mk_bin And a b
let mk_or  a b = mk_bin Or a b

let mk_not a = mk_un Lognot a

let mk_implies a b =
  mk_or (mk_not a) b

(* -------------------------------------------------- *)
(* Global state *)
(* -------------------------------------------------- *)

let new_commute_blocks = ref []

let fragment_env : (id, block node) Hashtbl.t =
  Hashtbl.create 32

let gc_list = ref []

let inferred_phi : exp node option ref = ref None

let reset () =
  infer := false;
  verify := false;
  new_commute_blocks := [];
  Hashtbl.clear fragment_env;
  gc_list := [];
  inferred_phi := None

(* -------------------------------------------------- *)
(* Invariant setup *)
(* -------------------------------------------------- *)

type examples_spec =
  {
    invariant : exp node;
    phi : exp node;
  }

(* -------------------------------------------------- *)
(* Utility helpers *)
(* -------------------------------------------------- *)

let choose_cond default phi =
  if !verify then PhiExp phi
  else if !infer then default
  else failwith "This works only with Infer or Verify"

let find_fragment id =
  match Hashtbl.find_opt fragment_env id with
  | Some blk -> blk
  | None -> failwith ("Unknown fragment: " ^ id)

let rec insert_one_before_end new_l l =
  match l with
  | [] -> new_l
  | [last] -> new_l @ [last]
  | head :: tail -> head :: insert_one_before_end new_l tail


(* -------------------------------------------------- *)
(* Loop extraction *)
(* -------------------------------------------------- *)

let block_has_loop (b : block node) =
  List.exists
    (function
      | { elt = While _; _ } -> true
      | _ -> false)
    b.elt

let extract_loop_body (b : block node) =
  match b.elt with
  | [ { elt = While (cond, invariant, body); _ } ] ->
      begin match invariant with
      | None -> failwith "You need to provide the loop invariant"
      | Some inv -> (cond, inv, body)
      end
  | _ ->
      failwith "Expected a single While loop block"

let split_S_C1 = function
  | [b1; b2] ->
      if block_has_loop b1 then
        let cond, invariant, body = extract_loop_body b1 in
        (cond, invariant, body, b2)
      else if block_has_loop b2 then
        let cond, invariant, body = extract_loop_body b2 in
        (cond, invariant, body, b1)
      else
        failwith "Expected one loop block"

  | _ ->
      failwith "Expected exactly two blocks"

(* -------------------------------------------------- *)
(* Commute premise generation *)
(* -------------------------------------------------- *)

let mk_commute cv cc b1 b2 pre post loc =
  { elt = Commute (cv, cc, [b1; b2], pre, post); loc }

let commute_premises cv cc blocks loc =
  let loop_cond, loop_invariant, block_S, block_C1 =
    split_S_C1 blocks
  in
  let exp_I = loop_invariant in

  let exp_phi =
    match !inferred_phi with
    | Some p -> p
    | None   -> failwith "Cannot synthesize the phi for phi => C1 |><| S"
  in

  let cond_true =
    choose_cond cc true_exp
  in

  let cond_phi =
    choose_cond cc exp_phi
  in

  let mk_local_commute pre post =
    mk_commute cv cond_true
      block_C1
      empty_blk
      pre
      post
      loc
  in

  (* 1. {I ∧ B} S {I ∧ φ} *)
  let premise1 =
    mk_commute cv cond_true
      empty_blk
      block_S
      (Some (mk_and exp_I loop_cond))
      (Some (mk_and exp_I exp_phi))
      loc
  in

  (* 2. {I} C1 {I} *)
  let premise2 =
    mk_local_commute
      (Some exp_I)
      (Some exp_I)
  in

  (* 3. {I ∧ B} C1 {B} *)
  let premise3 =
    mk_local_commute
      (Some (mk_and exp_I loop_cond))
      (Some loop_cond)
  in

  (* 4. {I ∧ ¬B} C1 {¬B} *)
  let premise4 =
    let nb = mk_not loop_cond in
    mk_local_commute
      (Some (mk_and exp_I nb))
      (Some nb)
  in

  (* 5. φ ⇒ C1 ⋈ S *)
  let premise5 =
    mk_commute cv cond_phi
      block_C1
      block_S
      None
      None
      loc
  in

  [ premise1; premise2; premise3; premise4; premise5 ]

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
      [node_up s (If (e, rewrite_block b1, rewrite_block b2))]

  | While (e, i, b) ->
      [ node_up s (While (e, i, rewrite_block b)) ]

  | For (i, c, st, b) ->
      [node_up s (For (i, c, st, rewrite_block b))]

  | SBlock (None, b) ->
      [node_up s (SBlock (None, rewrite_block b))]

  | Commute (cv, cc, blocks, _, _) ->
      commute_premises cv cc blocks s.loc

  | _ ->
      [s]

(* -------------------------------------------------- *)
(* Fragment collection *)
(* -------------------------------------------------- *)

let rec collect_stmt (s : stmt node) =
  match s.elt with
  | SBlock (Some (label, _), block) ->
      Hashtbl.replace fragment_env label block;
      []

  | If (e, b1, b2) ->
      [node_up s (If (e, collect_block b1, collect_block b2))]

  | While (e, i, b) ->
      [node_up s (While (e, i, collect_block b))]

  | For (i, c, st, b) ->
      [node_up s (For (i, c, st, collect_block b))]

  | _ ->
      [s]

and collect_block (b : block node) =
  node_app
    (fun stmts ->
      stmts
      |> List.map collect_stmt
      |> List.flatten)
    b

(* -------------------------------------------------- *)
(* Global commutativity rewriting *)
(* -------------------------------------------------- *)

let rewrite_global_commutativity gc_list =
  List.iter
    (fun gc ->
      let groups, cond, pre, post = gc.elt in

      let [@warning "-8"]
        [[(f1_id, _)]; [(f2_id, _)]] = groups
      in

      let block1 = find_fragment f1_id in
      let block2 = find_fragment f2_id in

      let stmt =
        mk_commute
          CommuteVarPar
          cond
          block1
          block2
          pre
          post
          block1.loc
      in

      new_commute_blocks :=
        !new_commute_blocks @ [stmt])
    gc_list

(* -------------------------------------------------- *)
(* Rewrite methods + program *)
(* -------------------------------------------------- *)

let rewrite_method (m : mdecl node) =
  node_app
    (fun m ->
      let new_body =
        collect_block m.body
      in

      rewrite_global_commutativity !gc_list;

      let new_body =
        {
          new_body with
          elt =
            insert_one_before_end
              !new_commute_blocks
              new_body.elt;
        }
      in

      {
        m with
        body =
          node_app
            (fun stmts ->
              stmts
              |> List.map rewrite_stmt
              |> List.flatten)
            new_body;
      })
    m

let rewrite_decl = function
  | Gmdecl m ->
      Gmdecl (rewrite_method m)

  | Commutativity gcList ->
      gc_list := gcList;
      Commutativity []

  | other ->
      other

(* Build a minimal program for pass 1 of two-pass verify: replace each
   Commute with a single `commute PhiInf { {C1} {S} }` (no pre/post).
   This lets us infer φ from just C1 ⋈ S without needing φ itself. *)
let extract_for_phi_infer (p : prog) : prog =
  let rewrite_stmt_for_phi (s : stmt node) =
    match s.elt with
    | Commute (cv, _cc, blocks, _pre, _post) ->
        let _loop_cond, _loop_inv, block_S, block_C1 = split_S_C1 blocks in
        [ { s with elt = Commute (cv, PhiInf, [block_C1; block_S], None, None) } ]
    | _ -> [s]
  in
  let rewrite_block_for_phi b =
    node_app (fun stmts -> stmts |> List.map rewrite_stmt_for_phi |> List.flatten) b
  in
  let rewrite_method_for_phi m =
    node_app (fun m -> { m with body = rewrite_block_for_phi m.body }) m
  in
  List.map (function
    | Gmdecl m -> Gmdecl (rewrite_method_for_phi m)
    | other -> other) p

let rewrite_program (p : prog) mode =
  set_mode mode;
  List.map rewrite_decl p