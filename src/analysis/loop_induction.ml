open Ast
open Ast_print
open Format
open Range
open Util
open Stdlib

let infer = ref false
let verify = ref false

let true_exp : exp node =
  no_loc (CBool true)

let empty_block : block node =
  no_loc []
  
let mk_and a b = no_loc (Bop (And, a, b))
let mk_not a   = no_loc (Uop (Lognot, a))

let mk_or e1 e2 =
  no_loc (Bop (Or, e1, e2))

let mk_id x = no_loc (Id x)

let mk_add a b = no_loc (Bop (Add, a, b))
let mk_sub a b = no_loc (Bop (Sub, a, b))

let mk_eq a b  = no_loc (Bop (Eq, a, b))

let mk_lte a b  = no_loc (Bop (Lte, a, b))
let mk_int n = no_loc (CInt (Int64.of_int n))

let mk_implies j phi =
  mk_or (mk_not j) phi

(* Assume we currently have these *)
(* let exp_I  = no_loc (CBool true) *)
(* let exp_I = no_loc
    (Bop (
      Eq,
      no_loc (Id "c"),
      no_loc (Bop (
        Add,
        no_loc (Id "c_init"),
        no_loc (Bop (
          Sub,
          no_loc (Id "x"),
          no_loc (Id "x_init")
        ))
      ))
    )) *)

(* base = c0 + (x - x0) *)
let base =
  mk_add (mk_id "c_init")
         (mk_sub (mk_id "x") (mk_id "x_init"))

(* inv1: c == base *)
let inv1 =
  mk_eq (mk_id "c") base

(* inv2: c == base - 1 *)
let inv2 =
  mk_eq (mk_id "c")
        (mk_sub base (mk_int 1))

(* I = inv1 OR inv2 *)
let exp_I = mk_lte (mk_id "c") base
  (* mk_or inv1 inv2 *)

(* let exp_J  = no_loc (CBool true) *)
let exp_J = exp_I
let exp_phi' = no_loc (Bop (Gt, no_loc (Id "c"), no_loc(CInt 0L)))
(* TODO: for now, we have only one loop*)
let exp_B  = ref (no_loc (CBool true))

(* J ⇒ φ′ (¬J∨φ′)*) 
let implies_exp = mk_implies exp_J exp_phi'
  
let block_has_loop (b : block node) : bool =
  List.exists
    (fun s ->
      match s.elt with
      | While _ -> true
      | _ -> false
    )
    b.elt
    
let rewrite_loop (b : block node) : block node =
  match b.elt with
  | [ { elt = While (cond, body); _ } ] ->
      exp_B := cond;
      body
  (** TODO: also add for loop *)
  | _ ->
      b

let split_S_C1 (blocks : block node list) : block node * block node =
  match List.partition block_has_loop blocks with
  | [s_block], [c1_block] ->
      (rewrite_loop s_block, c1_block)

  | _ ->
      failwith "Expected exactly one loop-containing block in commute"
    
let mk_commute cv cc b1 b2 pre post l =
  {elt= (Commute (cv, cc, [b1; b2], pre, post)); loc= l}


let commute_premises cv cc blocks loc =
  let (block_S, block_C1) = split_S_C1 blocks in

  (* 1. {J ∧ B} S {J} *)
  let cond = if !verify then (PhiExp (no_loc (CBool true))) else cc 
  in
  let s1 = mk_commute cv cond
    empty_block block_S
    (Some (mk_and exp_J !exp_B))
    (Some exp_J)
    loc

  in
    
  (* 2. J ⇒ φ′ *) 
  (* let s2 = mk_commute cv cc
    (no_loc [no_loc (Assert (mk_implies exp_J exp_phi'))]) empty_block
    None None
    loc *)
  let s2 = no_loc (Assert (implies_exp))
  
  in

  (* 3. φ′ ⇒ C1 ▷◁ S *)
  let cond = if !verify then (PhiExp exp_phi') else cc 
  in
  let s3 = mk_commute cv cond
    block_C1 block_S
    None None
    loc
  
  in

  (* 4. {I} C1 {I} *)
  let cond = if !verify then (PhiExp (no_loc (CBool true))) else cc 
  in
  let s4 = mk_commute cv cond
    block_C1 empty_block
    (Some exp_I)
    (Some exp_I)
    loc
  
  in

  (* 5. {¬B} C1 {¬B} *)
  let cond = if !verify then (PhiExp (no_loc (CBool true))) else cc 
  in
  let s5 = mk_commute cv cond
    block_C1 empty_block
    (Some (mk_not !exp_B))
    (Some (mk_not !exp_B))
    loc

  in
  [s1;s2;s3;s4;s5]


let rewrite_commute_stmt (s : stmt node) : stmt node list =
  match s.elt with
  | Commute (cv, cc, blocks, _pre, _post) ->
      commute_premises cv cc blocks s.loc
  | _ -> [s]
      

        
let rewrite_block (b : block node) : block node =
  node_app
    (fun stmts ->
      stmts
      |> List.map rewrite_commute_stmt
      |> List.flatten
    )
    b

      
let rewrite_stmt (s : stmt node) : stmt node list =
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
  
let rewrite_method (m : mdecl node) : mdecl node =
  node_app
    (fun m ->
      { m with body =
          node_app
            (fun stmts ->
              stmts
              |> List.map rewrite_stmt
              |> List.flatten
            )
            m.body
      }
    )
    m
  

let rewrite_decl (d : decl) : decl =
  match d with
  | Gmdecl m -> Gmdecl (rewrite_method m)
  | other -> other

let rewrite_program (p : prog) (mode: string) : prog =
  if (String.equal mode "infer") then
    infer := true
  else if (String.equal mode "verify") then
    verify := true;

  List.map rewrite_decl p

(** TODO: check if we have the pattern C1 and loop; for now assume*)