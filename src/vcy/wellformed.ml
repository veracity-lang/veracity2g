open Ast

(* Well-formedness of commutativity specification entries (Def. well-formed
   in the POPL'27 paper; W1 in rocq/Commutativity.v).

   (W1) Parameters are read-only: no NCB of an entry assigns a parameter of
   any NCB of that entry.  Storing into an array, hashtable, struct or heap
   cell counts as assigning the variable it is reached through, as CStore does
   in the Rocq semantics.  Variables declared in a body are not parameters, so
   assigning them is fine even if they shadow one.  Code outside the bodies
   may assign parameters: that is what a loop increment does.

   (Scope) A condition names only the parameters of the two labels it relates
   and globals.  The scheduler evaluates it over just those bindings
   (interp_phi_two), so a local of main would be IdNotFound at run time even
   though verify, which treats it as state, accepts it. *)

(* The variable that an lvalue or a label parameter is reached through. *)
let rec root (e : exp node) : id option =
  match e.elt with
  | Id x -> Some x
  | Index (e, _) | Proj (e, _) | HDerefValue e | HDerefNext e -> root e
  | _ -> None

let sub_exps (e : exp node) : exp node list =
  match e.elt with
  | CArr (_, l) | CallRaw (_, l) | Call (_, l) -> l
  | NewArr (_, e) | Uop (_, e) | Proj (e, _) | HDerefValue e | HDerefNext e
  | Exists (_, _, e) | Forall (_, _, e) -> [e]
  | Index (a, b) | Bop (_, a, b) | HeapAlloc (a, b) | HeapValue (a, b) -> [a; b]
  | Ternary (a, b, c) -> [a; b; c]
  | CStruct (_, fs) -> List.map snd fs
  | _ -> []

(* Library methods that store through their first argument. *)
let stores_through_first_arg = ["ht_put"; "heap_write"]

(* Variables a block assigns, each with the location of the write. *)
let rec writes_of_block (g : global_env) (seen : id list) (bound : id list)
    (b : block) : (id * Range.t) list =
  match b with
  | [] -> []
  | s :: tl ->
    let exps = List.concat_map (writes_of_exp g seen bound) in
    let blk = writes_of_block g seen bound in
    let assigned e =
      match root e with
      | Some x when not (List.mem x bound) -> [x, s.loc]
      | _ -> [] in
    let here, bound' =
      match s.elt with
      | Assn (l, r) -> assigned l @ exps [l; r], bound
      | Havoc e -> assigned e @ exps [e], bound
      | Decl (x, (_, e)) -> exps [e], x :: bound
      | SCallRaw (f, args) | SCall ((MethodM (f, _) | MethodL (f, _)), args) ->
        writes_of_call g seen bound f args @ exps args, bound
      | Ret eo -> exps (Option.to_list eo), bound
      | Raise e | Assert e | Assume e | Require e -> exps [e], bound
      | If (e, b1, b2) -> exps [e] @ blk b1.elt @ blk b2.elt, bound
      | While (e, _, b) -> exps [e] @ blk b.elt, bound
      | For (vds, eo, so, b) ->
        let bound_in = List.map fst vds @ bound in
        exps (List.map (fun (_, (_, e)) -> e) vds)
        @ List.concat_map (writes_of_exp g seen bound_in) (Option.to_list eo)
        @ writes_of_block g seen bound_in (Option.to_list so @ b.elt),
        bound
      | SBlock (_, b) -> blk b.elt, bound
      | Commute (_, _, bl, _, _) -> List.concat_map (fun b -> blk b.elt) bl, bound
      | SendDep _ | SendEOP _ -> [], bound
    in
    here @ writes_of_block g seen bound' tl

and writes_of_exp g seen bound (e : exp node) : (id * Range.t) list =
  let inner = List.concat_map (writes_of_exp g seen bound) (sub_exps e) in
  match e.elt with
  | CallRaw (f, args) | Call ((MethodM (f, _) | MethodL (f, _)), args) ->
    List.map (fun (x, _) -> x, e.loc) (writes_of_call g seen bound f args) @ inner
  | _ -> inner

(* A callee's writes, seen from the call: an array formal stands for the root
   of its argument, and what is left of the callee's writes are globals. *)
and writes_of_call g seen bound f (args : exp node list) : (id * Range.t) list =
  let free e =
    match root e with
    | Some x when not (List.mem x bound) -> [x, e.loc]
    | _ -> [] in
  if List.mem f stores_through_first_arg then
    match args with a :: _ -> free a | [] -> []
  else
    match List.assoc_opt f g.methods with
    | Some (m : tmethod) when not (List.mem f seen) ->
      let formals = List.map fst m.args in
      List.concat_map (fun (x, loc) ->
        match List.find_index (String.equal x) formals with
        | Some i when i < List.length args -> free (List.nth args i)
        | Some _ -> []
        | None -> if List.mem x bound then [] else [x, loc])
        (writes_of_block g (f :: seen) [] m.body.elt)
    | _ -> []

(* Every NCB instance in the program, by label. *)
let rec labeled_in_block (b : block) : (id * (exp node list * block node)) list =
  List.concat_map (fun (s : stmt node) ->
    match s.elt with
    | SBlock (Some (l, ps), b) ->
      (l, (Option.value ~default:[] ps, b)) :: labeled_in_block b.elt
    | SBlock (None, b) | While (_, _, b) | For (_, _, _, b) -> labeled_in_block b.elt
    | If (_, b1, b2) -> labeled_in_block b1.elt @ labeled_in_block b2.elt
    | Commute (_, _, bl, _, _) -> List.concat_map (fun b -> labeled_in_block b.elt) bl
    | _ -> []) b

(* One message for each write that breaks (W1) and each NCB whose parameter it
   assigns, however many entries they share. *)
let w1_violations (g : global_env) : string list =
  let ncbs = List.concat_map (fun (_, (m : tmethod)) -> labeled_in_block m.body.elt) g.methods in
  List.concat_map (fun (gc : group_commute node) ->
    let labels, _ = gc.elt in
    let entry = List.sort_uniq compare (List.map fst (List.concat labels)) in
    let instances = List.concat_map (fun l ->
      List.filter_map (fun (l', n) -> if l = l' then Some (l, n) else None) ncbs) entry in
    let params = List.concat_map (fun (l, (ps, _)) ->
      List.filter_map (fun p -> Option.map (fun x -> x, l) (root p)) ps) instances in
    List.concat_map (fun (l, (_, (body : block node))) ->
      List.concat_map (fun (x, loc) ->
        List.filter_map (fun (p, owner) ->
          if String.equal p x then
            Some (Printf.sprintf
              "%s: W1 violation: NCB %s assigns %s, a parameter of NCB %s"
              (Range.string_of_range loc) l x owner)
          else None) params)
        (writes_of_block g [] [] body.elt)) instances)
    g.group_commute
  |> List.sort_uniq compare

(* Identifiers an expression reads, minus those a quantifier binds. *)
let rec free_ids (e : exp node) : (id * Range.t) list =
  match e.elt with
  | Id x -> [x, e.loc]
  | Exists (x, _, b) | Forall (x, _, b) ->
    List.filter (fun (y, _) -> not (String.equal x y)) (free_ids b)
  | _ -> List.concat_map free_ids (sub_exps e)

(* One message for each identifier a condition reads that is neither a global
   nor a parameter of every pair of labels the condition relates. *)
let scope_violations (g : global_env) : string list =
  let params (_, ps) = List.filter_map root (Option.value ~default:[] ps) in
  List.concat_map (fun (gc : group_commute node) ->
    match gc.elt with
    | _, PhiInf -> []
    | sides, PhiExp phi ->
      let rec pairs = function
        | [] -> []
        | s :: tl -> List.concat_map (fun s' ->
            List.concat_map (fun a -> List.map (fun b -> a, b) s') s) tl @ pairs tl in
      List.concat_map (fun (a, b) ->
        let bound = params a @ params b in
        List.filter_map (fun (x, loc) ->
          if List.mem x bound || List.mem_assoc x g.globals then None
          else Some (Printf.sprintf
            "%s: scope violation: the condition for %s and %s reads %s, \
             which is neither a parameter of either label nor a global"
            (Range.string_of_range loc) (fst a) (fst b) x))
          (free_ids phi))
        (pairs sides))
    g.group_commute
  |> List.sort_uniq compare

let check (g : global_env) : unit =
  match w1_violations g @ scope_violations g with
  | [] -> ()
  | vs -> List.iter prerr_endline vs; exit 1
