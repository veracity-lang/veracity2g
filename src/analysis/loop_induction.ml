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

(* -------------------------------------------------- *)
(* Invariant setup *)
(* -------------------------------------------------- *)

let file_name = ref ""

type examples_spec =
  {
    invariant : exp node;
    phi : exp node;
  }

(* let benchmarks : (string, examples_spec) Hashtbl.t =
  Hashtbl.create 20 *)

let example1 = {invariant = mk_bin Gte (mk_id "c") zero; phi = mk_bin Neq (mk_id "c") zero}

(* let _ = Hashtbl.add benchmarks "example1" example1 *)

(* phi: !(0 == i) && !(1 == a[0]) || 1 == a[0] *)
let example2 = {invariant = mk_bin Gte (mk_id "i") zero; phi = mk_bin Gt (mk_id "i") zero}

(* let _ = Hashtbl.add benchmarks "example2" example2 *)

(* I: i % 2 = 0 ∧ i ≥ 0
  phi: (i % 2 == 0 && (ctr > 0 && amt > 0 || ctr <= 0 && amt < -ctr)) *)
let example3 = {
  invariant = mk_bin And
  (mk_bin Eq
     (mk_bin Mod (mk_id "i") (mk_int 2))
     zero)
  (mk_bin Gte (mk_id "i") zero);
  phi = mk_bin And
  (mk_bin Eq
     (mk_bin Mod (mk_id "i") (mk_int 2))
     zero)
  (mk_bin Or
     (mk_bin And
        (mk_bin Gt (mk_id "ctr") zero)
        (mk_bin Gt (mk_id "amt") zero))
     (mk_bin And
        (mk_bin Lte (mk_id "ctr") zero)
        (mk_bin Lt (mk_id "amt")
          (mk_un Neg (mk_id "ctr")))))}

(* let _ = Hashtbl.add benchmarks "example3" example3 *)

let example4 = {
  invariant = mk_bin And (mk_bin Gte (mk_id "i") zero) (mk_bin Lte (mk_id "i") (mk_id "n")); 
  phi = mk_bin Gt (mk_id "balance") (mk_id "fee")}

(* let _ = Hashtbl.add benchmarks "example4" example4 *)

(* let exp_I = (Hashtbl.find benchmarks !file_name).invariant
let exp_phi' = (Hashtbl.find benchmarks !file_name).phi *)
let exp_I = example1.invariant
let exp_phi' = example1.phi
(* -------------------------------------------------- *)
(* Utility helpers *)
(* -------------------------------------------------- *)

let choose_cond default phi =
  if !verify then PhiExp phi else default

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
  | [ { elt = While (cond, _, body); _ } ] -> (** TODO: used Inv in while *)
      (cond, body)
  | _ ->
      failwith "Expected a single While loop block"

let split_S_C1 = function
  | [b1; b2] ->
      if block_has_loop b1 then
        let cond, body = extract_loop_body b1 in
        (cond, body, b2)
      else if block_has_loop b2 then
        let cond, body = extract_loop_body b2 in
        (cond, body, b1)
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
  let loop_cond, block_S, block_C1 =
    split_S_C1 blocks
  in

  let cond_true =
    choose_cond cc true_exp
  in

  let cond_phi =
    choose_cond cc exp_phi'
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
      (Some (mk_and exp_I exp_phi'))
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

  | While (e, b) ->
      [node_up s (While (e, collect_block b))]

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

let rewrite_program (p_name: string) (p : prog) mode =
  (* Printf.printf "-> %s \n" p_name; *)
  file_name := p_name;
  set_mode mode;
  List.map rewrite_decl p