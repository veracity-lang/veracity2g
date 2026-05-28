open Ast

(* ---- AST helpers ---- *)

let make_lock id =
  no_loc @@ SCallRaw ("mutex_lock", [no_loc @@ CInt (Int64.of_int id)])

let make_unlock id =
  no_loc @@ SCallRaw ("mutex_unlock", [no_loc @@ CInt (Int64.of_int id)])

(* wrap_with_lock id [s1;s2;...] = [lock; s1; s2; ...; unlock] *)
let wrap_with_lock id stmts =
  [make_lock id] @ stmts @ [make_unlock id]

(* ---- Global variable collection ---- *)

let collect_globals (prog : prog) : id list =
  List.filter_map (function
    | Gvdecl { elt = { name; _ }; _ } -> Some name
    | _ -> None
  ) prog

(* ---- Expression / statement utilities ---- *)

let rec ids_in_exp (e : exp) : id list =
  match e with
  | Id id -> [id]
  | Index (e1, e2) -> ids_in_exp e1.elt @ ids_in_exp e2.elt
  | Bop (_, e1, e2) -> ids_in_exp e1.elt @ ids_in_exp e2.elt
  | Uop (_, e) -> ids_in_exp e.elt
  | CallRaw (_, args) | Call (_, args) ->
    List.concat_map (fun a -> ids_in_exp a.elt) args
  | Ternary (e1, e2, e3) ->
    ids_in_exp e1.elt @ ids_in_exp e2.elt @ ids_in_exp e3.elt
  | CArr (_, es) -> List.concat_map (fun e -> ids_in_exp e.elt) es
  | CStruct (_, bindings) -> List.concat_map (fun (_, e) -> ids_in_exp e.elt) bindings
  | Proj (e, _) | NewArr (_, e) -> ids_in_exp e.elt
  | _ -> []

let rec ids_in_stmts (stmts : stmt node list) : id list =
  List.concat_map (fun s -> ids_in_stmt s.elt) stmts

and ids_in_stmt (s : stmt) : id list =
  match s with
  | Assn (lhs, rhs) -> ids_in_exp lhs.elt @ ids_in_exp rhs.elt
  | Decl (_, (_, rhs)) -> ids_in_exp rhs.elt
  | Ret (Some e) -> ids_in_exp e.elt
  | Ret None -> []
  | SCallRaw (_, args) | SCall (_, args) ->
    List.concat_map (fun a -> ids_in_exp a.elt) args
  | If (cond, b1, b2) ->
    ids_in_exp cond.elt @ ids_in_stmts b1.elt @ ids_in_stmts b2.elt
  | While (cond, body) -> ids_in_exp cond.elt @ ids_in_stmts body.elt
  | For (_, eo, _, body) ->
    (match eo with Some e -> ids_in_exp e.elt | None -> []) @
    ids_in_stmts body.elt
  | Commute (_, _, blocks, _, _) ->
    List.concat_map (fun b -> ids_in_stmts b.elt) blocks
  | SBlock (_, body) -> ids_in_stmts body.elt
  | Assert e | Assume e | Require e | Raise e -> ids_in_exp e.elt
  | Havoc _ | SendDep _ | SendEOP _ -> []

let local_decl_names (stmts : stmt node list) : id list =
  List.filter_map (fun s ->
    match s.elt with Decl (name, _) -> Some name | _ -> None
  ) stmts

(* Free variables: ids used in block body but not declared inside it *)
let outer_vars_of_block (stmts : stmt node list) : id list =
  let used   = ids_in_stmts stmts |> List.sort_uniq compare in
  let locals = local_decl_names stmts in
  List.filter (fun id -> not (List.mem id locals)) used

(* ---- Commutativity condition analysis ---- *)

let rec extract_diseqs (e : exp) : (id * id) list =
  match e with
  | Bop (Neq, {elt = Id a; _}, {elt = Id b; _}) -> [(a, b); (b, a)]
  | Bop (And, e1, e2) -> extract_diseqs e1.elt @ extract_diseqs e2.elt
  | _ -> []

(* Which argument positions are guaranteed distinct across concurrent instances *)
let safe_positions_of_gc (gc : group_commute node) : int list =
  let (groups, cond) = gc.elt in
  match cond with
  | PhiInf -> []
  | PhiExp phi ->
    let diseqs = extract_diseqs phi.elt in
    let all_params =
      List.concat_map (fun group ->
        List.concat_map (fun (_label, params_opt) ->
          match params_opt with
          | None -> []
          | Some params ->
            List.filter_map Fun.id @@
            List.mapi (fun i p ->
              match p.elt with Id name -> Some (name, i) | _ -> None) params
        ) group
      ) groups
    in
    List.filter_map (fun (a, b) ->
      match List.assoc_opt a all_params, List.assoc_opt b all_params with
      | Some pa, Some pb when pa = pb -> Some pa
      | _ -> None
    ) diseqs
    |> List.sort_uniq compare

(* Build map: block_label_id -> safe_positions *)
let build_safe_pos_map (prog : prog) : (id * int list) list =
  let gcs =
    List.filter_map (function
      | Commutativity nodes -> Some nodes | _ -> None
    ) prog |> List.concat
  in
  List.concat_map (fun gc ->
    let (groups, _) = gc.elt in
    let safe_pos = safe_positions_of_gc gc in
    if safe_pos = [] then []
    else
      List.concat_map (fun group ->
        List.map (fun (label, _) -> (label, safe_pos)) group
      ) groups
  ) gcs

(* Map safe positions to actual argument names in a block instantiation *)
let safe_arg_names (params : exp node list) (safe_pos : int list) : id list =
  List.filter_map (fun i ->
    if i < List.length params then
      match (List.nth params i).elt with Id name -> Some name | _ -> None
    else None
  ) safe_pos

(* ---- Conflict detection ---- *)

(* An access to `var` with index `idx_opt` is conflicting if:
   - var is in outer_vars, AND
   - the index is not a safe arg *)
let is_conflicting (outer_vars : id list) (safe_args : id list) (var : id) (idx_opt : exp option) : bool =
  if not (List.mem var outer_vars) then false
  else match idx_opt with
  | None -> true
  | Some (Id safe) when List.mem safe safe_args -> false
  | _ -> true

(* Root variable and optional index from an lvalue expression *)
let access_var_idx (e : exp) : (id * exp option) option =
  match e with
  | Id id -> Some (id, None)
  | Index ({elt = Id id; _}, {elt = idx; _}) -> Some (id, Some idx)
  | _ -> None

(* Variables WRITTEN (conflicting) by a statement, recursively *)
let rec conflicting_writes_in_stmts (outer_vars : id list) (safe_args : id list) (stmts : stmt node list) : id list =
  List.concat_map (fun s -> conflicting_writes_of_stmt outer_vars safe_args s.elt) stmts
  |> List.sort_uniq compare

and conflicting_writes_of_stmt outer_vars safe_args s =
  match s with
  | Assn ({elt = lhs; _}, _) ->
    (match access_var_idx lhs with
     | Some (v, idx) when is_conflicting outer_vars safe_args v idx -> [v]
     | _ -> [])
  | SCallRaw ("ht_put", ({elt = Id id; _}) :: ({elt = key; _}) :: _) ->
    if is_conflicting outer_vars safe_args id (Some key) then [id] else []
  | If (_, b1, b2) ->
    conflicting_writes_in_stmts outer_vars safe_args b1.elt @
    conflicting_writes_in_stmts outer_vars safe_args b2.elt
  | While (_, body) | For (_, _, _, body) | SBlock (_, body) ->
    conflicting_writes_in_stmts outer_vars safe_args body.elt
  | Commute (_, _, blocks, _, _) ->
    List.concat_map (fun b -> conflicting_writes_in_stmts outer_vars safe_args b.elt) blocks
  | _ -> []

(* Does an expression read a conflicting variable of the given name? *)
let rec exp_reads_var (var : id) (e : exp) : bool =
  match e with
  | Id v -> v = var
  | Index ({elt = Id id; _}, _) -> id = var
  | CallRaw ("ht_get", ({elt = Id id; _}) :: _) -> id = var
  | Bop (_, e1, e2) -> exp_reads_var var e1.elt || exp_reads_var var e2.elt
  | Uop (_, e) -> exp_reads_var var e.elt
  | CallRaw (_, args) | Call (_, args) ->
    List.exists (fun a -> exp_reads_var var a.elt) args
  | Ternary (e1, e2, e3) ->
    exp_reads_var var e1.elt || exp_reads_var var e2.elt || exp_reads_var var e3.elt
  | _ -> false

(* Does a statement's RHS / args read a given variable? *)
let stmt_reads_var (var : id) (s : stmt) : bool =
  match s with
  | Decl (_, (_, {elt = rhs; _})) -> exp_reads_var var rhs
  | Assn (_, {elt = rhs; _}) -> exp_reads_var var rhs
  | SCallRaw (_, args) | SCall (_, args) ->
    List.exists (fun a -> exp_reads_var var a.elt) args
  | _ -> false

(* ---- Check for existing locks ---- *)

let rec block_has_mutex (stmts : stmt node list) : bool =
  List.exists (fun s ->
    match s.elt with
    | SCallRaw ("mutex_lock", _) | SCallRaw ("mutex_unlock", _) -> true
    | If (_, b1, b2) -> block_has_mutex b1.elt || block_has_mutex b2.elt
    | While (_, b) | For (_, _, _, b) | SBlock (_, b) -> block_has_mutex b.elt
    | _ -> false
  ) stmts

(* ---- Cross-block conflict analysis ---- *)

(* Find all named SBlocks in a statement list (recursively) *)
let rec named_sblocks_in_stmts (stmts : stmt node list) : (id * exp node list option * stmt node list) list =
  List.concat_map (fun s -> named_sblocks_in_stmt s.elt) stmts

and named_sblocks_in_stmt = function
  | SBlock (Some (label, params_opt), body) ->
    (label, params_opt, body.elt) :: named_sblocks_in_stmts body.elt
  | SBlock (None, body) -> named_sblocks_in_stmts body.elt
  | If (_, b1, b2) ->
    named_sblocks_in_stmts b1.elt @ named_sblocks_in_stmts b2.elt
  | While (_, body) | For (_, _, _, body) -> named_sblocks_in_stmts body.elt
  | Commute (_, _, blocks, _, _) ->
    List.concat_map (fun b -> named_sblocks_in_stmts b.elt) blocks
  | _ -> []

let find_all_named_sblocks (prog : prog) : (id * exp node list option * stmt node list) list =
  List.filter_map (function Gmdecl d -> Some d | _ -> None) prog
  |> List.concat_map (fun d -> named_sblocks_in_stmts d.elt.body.elt)

(* Compute the set of variables that are truly conflicting across concurrent blocks.
   A variable is inter-block conflicting if it is written (with non-safe indexing) by
   at least two distinct label types in the same group_commute, OR by a label type that
   appears in multiple groups (same-type multiple-instances). *)
let compute_inter_block_conflict_set
    (prog : prog)
    (safe_pos_map : (id * int list) list)
    : id list =
  let gcs =
    List.filter_map (function
      | Commutativity nodes -> Some nodes | _ -> None
    ) prog |> List.concat
  in
  let all_blocks = find_all_named_sblocks prog in
  (* Group blocks by label *)
  let blocks_by_label : (id * (exp node list option * stmt node list) list) list =
    List.fold_left (fun acc (label, params_opt, body) ->
      let existing = Option.value ~default:[] (List.assoc_opt label acc) in
      (label, (params_opt, body) :: existing) :: List.remove_assoc label acc
    ) [] all_blocks
  in
  List.concat_map (fun gc ->
    let (groups, _) = gc.elt in
    let all_labels_in_gc = List.concat groups |> List.map fst |> List.sort_uniq compare in
    (* Which labels appear in multiple groups (same-type parallel) *)
    let multi_instance_labels =
      List.filter (fun label ->
        let count = List.length (List.filter (fun g -> List.exists (fun (l,_) -> l = label) g) groups) in
        count > 1
      ) all_labels_in_gc
    in
    (* For each label in gc, compute its write set (using safe_args from actual block params) *)
    (* Use safe positions specific to THIS gc (not the global map), so that
       labels appearing in multiple gcs with different safe positions are
       analysed correctly for this particular concurrency context. *)
    let gc_safe_pos = safe_positions_of_gc gc in
    let per_label_writes : (id * id list) list =
      List.filter_map (fun label ->
        match List.assoc_opt label blocks_by_label with
        | None -> None
        | Some instances ->
          let writes =
            List.concat_map (fun (params_opt, body) ->
              let safe_args = match params_opt with
                | Some ps -> safe_arg_names ps gc_safe_pos
                | None -> []
              in
              let outer = outer_vars_of_block body in
              conflicting_writes_in_stmts outer safe_args body
            ) instances
            |> List.sort_uniq compare
          in
          Some (label, writes)
      ) all_labels_in_gc
    in
    (* Collect vars written by multiple labels or by multi-instance labels *)
    let var_to_labels : (id * id list) list =
      List.fold_left (fun acc (label, writes) ->
        List.fold_left (fun acc v ->
          let existing = Option.value ~default:[] (List.assoc_opt v acc) in
          if List.mem label existing then acc
          else (v, label :: existing) :: List.remove_assoc v acc
        ) acc writes
      ) [] per_label_writes
    in
    List.filter_map (fun (v, labels_writing) ->
      let has_multiple_label_types = List.length labels_writing >= 2 in
      let has_multi_instance = List.exists (fun l -> List.mem l multi_instance_labels) labels_writing in
      if has_multiple_label_types || has_multi_instance then Some v else None
    ) var_to_labels
  ) gcs
  |> List.sort_uniq compare

(* ---- Lock ID state ---- *)

type lock_state = {
  mutable var_to_lock : (id * int) list;
  mutable next_id     : int;
}

let create_lock_state () = { var_to_lock = []; next_id = 0 }

let get_lock (st : lock_state) (var : id) : int =
  match List.assoc_opt var st.var_to_lock with
  | Some id -> id
  | None ->
    let id = st.next_id in
    st.var_to_lock <- (var, id) :: st.var_to_lock;
    st.next_id <- id + 1;
    id

(* ---- Core transformation ---- *)

(* The set of conflict_set vars directly written by a single top-level statement.
   Only Assn and ht_put count as writes.  If/While/For/SBlock return [] — we recurse. *)
let stmt_direct_writes (conflict_set : id list) (safe_args : id list) (s : stmt) : id list =
  match s with
  | Assn ({elt = lhs; _}, _) ->
    (match access_var_idx lhs with
     | Some (v, idx)
       when List.mem v conflict_set
         && is_conflicting conflict_set safe_args v idx -> [v]
     | _ -> [])
  | SCallRaw ("ht_put", ({elt = Id id; _}) :: ({elt = key; _}) :: _)
    when List.mem id conflict_set
      && is_conflicting conflict_set safe_args id (Some key) -> [id]
  | _ -> []

(* Detect the check-then-update pattern: If whose condition reads a conflict_set var
   that is also written in one of its branches.  In this case the whole If must be
   wrapped atomically. *)
let if_is_check_then_update conflict_set safe_args cond b1 b2 : id list =
  let cond_reads =
    List.filter (fun v ->
      List.mem v conflict_set && exp_reads_var v cond.elt
    ) conflict_set
  in
  if cond_reads = [] then []
  else
    let branch_writes =
      conflicting_writes_in_stmts conflict_set safe_args b1.elt @
      conflicting_writes_in_stmts conflict_set safe_args b2.elt
    in
    List.filter (fun v -> List.mem v branch_writes) cond_reads

(* Transform a block body, inserting locks around conflicting writes.
   Strategy:
   - Walk stmts left-to-right, grouping consecutive writes to the same var.
   - If the statement immediately preceding a write reads the same var, merge it
     into the group (backward extension for read-then-write atomicity).
   - For If/While/For/anonymous-SBlock with no direct write: recurse into sub-blocks. *)
let rec transform_stmts
    (conflict_set : id list)
    (safe_args    : id list)
    (lock_st      : lock_state)
    (stmts        : stmt node list)
    : stmt node list =
  (* Two-pass approach:
     Pass 1: build a list of (stmt, direct_write_var option).
     Pass 2: group and wrap. *)
  let annotated =
    List.map (fun stmt ->
      let writes = stmt_direct_writes conflict_set safe_args stmt.elt in
      let ctu = match stmt.elt with
        | If (cond, b1, b2) -> if_is_check_then_update conflict_set safe_args cond b1 b2
        | _ -> []
      in
      let var_opt = match writes @ ctu with v :: _ -> Some v | [] -> None in
      (stmt, var_opt)
    ) stmts
  in
  (* Group consecutive stmts that write the same var (with backward read extension) *)
  let rec group rev_acc pending_var pending_rev_group = function
    | [] ->
      let rev_acc = flush rev_acc pending_var pending_rev_group in
      List.rev rev_acc
    | (stmt, var_opt) :: rest ->
      (match var_opt with
      | None ->
        (* No direct write: flush current group, then recurse into nested structures *)
        let rev_acc = flush rev_acc pending_var pending_rev_group in
        let t = transform_single conflict_set safe_args lock_st stmt in
        group (t :: rev_acc) "" [] rest
      | Some v ->
        (* Look-back: if the current group is empty and the previous statement (head of rev_acc)
           is a plain read of v (and has no other writes), pull it into the group. *)
        let (rev_acc', read_ext) =
          if pending_var = "" then   (* starting a new group *)
            match rev_acc with
            | prev :: rest_acc when stmt_reads_var v prev.elt ->
              (rest_acc, [prev])   (* pull previous stmt into this group *)
            | _ -> (rev_acc, [])
          else (rev_acc, [])
        in
        if pending_var = v then
          (* Extend current group *)
          group rev_acc' v (stmt :: (read_ext @ pending_rev_group)) rest
        else begin
          (* Flush current group, start new one (with possible read extension) *)
          let rev_acc' = flush rev_acc' pending_var pending_rev_group in
          group rev_acc' v (stmt :: read_ext) rest
        end)
  and flush rev_acc pvar rev_group =
    match rev_group with
    | [] -> rev_acc
    | _ ->
      let lock_id = get_lock lock_st pvar in
      (* rev_group is in reverse order; transform each stmt, reverse to get correct order *)
      let group_stmts = List.rev_map (transform_single conflict_set safe_args lock_st) rev_group in
      let wrapped = wrap_with_lock lock_id group_stmts in
      (* Prepend (in reversed form) to rev_acc so that List.rev gives correct order *)
      List.rev_append wrapped rev_acc
  in
  group [] "" [] annotated

(* Recurse into nested control structures for stmts with no direct write *)
and transform_single
    (conflict_set : id list)
    (safe_args    : id list)
    (lock_st      : lock_state)
    (stmt         : stmt node)
    : stmt node =
  let elt' = match stmt.elt with
  | If (cond, b1, b2) ->
    (* If it's check-then-update, leave as-is for the caller to wrap *)
    if if_is_check_then_update conflict_set safe_args cond b1 b2 <> [] then stmt.elt
    else
      let b1' = { b1 with elt = transform_stmts conflict_set safe_args lock_st b1.elt } in
      let b2' = { b2 with elt = transform_stmts conflict_set safe_args lock_st b2.elt } in
      If (cond, b1', b2')
  | While (cond, body) ->
    While (cond, { body with elt = transform_stmts conflict_set safe_args lock_st body.elt })
  | For (decls, eo, so, body) ->
    For (decls, eo, so, { body with elt = transform_stmts conflict_set safe_args lock_st body.elt })
  | SBlock (None, body) ->
    SBlock (None, { body with elt = transform_stmts conflict_set safe_args lock_st body.elt })
  | SBlock (Some _, _) -> stmt.elt   (* named: handled at prog level *)
  | Commute (var, phi, blocks, pre, post) ->
    let blocks' = List.map (fun b ->
      { b with elt = transform_stmts conflict_set safe_args lock_st b.elt }) blocks in
    Commute (var, phi, blocks', pre, post)
  | other -> other
  in
  { stmt with elt = elt' }

(* ---- Program-level traversal ---- *)

let rec visit_stmts
    (conflict_set  : id list)
    (safe_pos_map  : (id * int list) list)
    (lock_st       : lock_state)
    (stmts         : stmt node list)
    : stmt node list =
  List.map (fun stmt ->
    { stmt with elt = visit_stmt conflict_set safe_pos_map lock_st stmt.elt }
  ) stmts

and visit_stmt conflict_set safe_pos_map lock_st s =
  match s with
  | SBlock (Some (label, params_opt), body) ->
    if block_has_mutex body.elt then s
    else begin
      let safe_pos  = Option.value ~default:[] (List.assoc_opt label safe_pos_map) in
      let safe_args = match params_opt with
        | Some ps -> safe_arg_names ps safe_pos | None -> []
      in
      let body' = { body with elt =
        transform_stmts conflict_set safe_args lock_st body.elt
      } in
      SBlock (Some (label, params_opt), body')
    end
  | SBlock (None, body) ->
    SBlock (None, { body with elt = visit_stmts conflict_set safe_pos_map lock_st body.elt })
  | If (cond, b1, b2) ->
    let b1' = { b1 with elt = visit_stmts conflict_set safe_pos_map lock_st b1.elt } in
    let b2' = { b2 with elt = visit_stmts conflict_set safe_pos_map lock_st b2.elt } in
    If (cond, b1', b2')
  | While (cond, body) ->
    While (cond, { body with elt = visit_stmts conflict_set safe_pos_map lock_st body.elt })
  | For (decls, eo, so, body) ->
    For (decls, eo, so, { body with elt = visit_stmts conflict_set safe_pos_map lock_st body.elt })
  | Commute (var, phi, blocks, pre, post) ->
    let blocks' = List.map (fun b ->
      { b with elt = visit_stmts conflict_set safe_pos_map lock_st b.elt }) blocks in
    Commute (var, phi, blocks', pre, post)
  | other -> other

(* ---- Top-level entry point ---- *)

let transform_prog (prog : prog) : prog =
  let safe_pos_map  = build_safe_pos_map prog in
  let conflict_set  = compute_inter_block_conflict_set prog safe_pos_map in
  if conflict_set = [] then prog  (* nothing to do *)
  else
    let lock_st = create_lock_state () in
    List.map (function
      | Gmdecl decl ->
        let body' = { decl.elt.body with elt =
          visit_stmts conflict_set safe_pos_map lock_st decl.elt.body.elt
        } in
        Gmdecl { decl with elt = { decl.elt with body = body' } }
      | other -> other
    ) prog
