open Ast
open Dswp_task

(* ---- AST helpers ---- *)

let make_lock id =
  no_loc @@ SCallRaw ("mutex_lock", [no_loc @@ CInt (Int64.of_int id)])

let make_unlock id =
  no_loc @@ SCallRaw ("mutex_unlock", [no_loc @@ CInt (Int64.of_int id)])

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
  | While (cond, _, body) -> ids_in_exp cond.elt @ ids_in_stmts body.elt
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

(* Free variables of a block body — used but not declared inside *)
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

(* Argument positions guaranteed distinct across concurrent instances *)
let safe_positions_of_gc (gc : group_commute node) : int list =
  let (groups, cond, _, _) = gc.elt in
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
    let (groups, _, _, _) = gc.elt in
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

let is_conflicting (outer_vars : id list) (safe_args : id list) (var : id) (idx_opt : exp option) : bool =
  if not (List.mem var outer_vars) then false
  else match idx_opt with
  | None -> true
  | Some (Id safe) when List.mem safe safe_args -> false
  | _ -> true

let access_var_idx (e : exp) : (id * exp option) option =
  match e with
  | Id id -> Some (id, None)
  | Index ({elt = Id id; _}, {elt = idx; _}) -> Some (id, Some idx)
  | _ -> None

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
  | While (_, _, body) | For (_, _, _, body) | SBlock (_, body) ->
    conflicting_writes_in_stmts outer_vars safe_args body.elt
  | Commute (_, _, blocks, _, _) ->
    List.concat_map (fun b -> conflicting_writes_in_stmts outer_vars safe_args b.elt) blocks
  | _ -> []

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
    | While (_, _, b) | For (_, _, _, b) | SBlock (_, b) -> block_has_mutex b.elt
    | _ -> false
  ) stmts

(* ---- Pre-DSWP: NCB conflict set from commutativity declarations ---- *)

(* Collect all named SBlocks recursively *)
let rec named_sblocks_in_stmts (stmts : stmt node list)
    : (id * exp node list option * stmt node list) list =
  List.concat_map (fun s -> named_sblocks_in_stmt s.elt) stmts

and named_sblocks_in_stmt = function
  | SBlock (Some (label, params_opt), body) ->
    (label, params_opt, body.elt) :: named_sblocks_in_stmts body.elt
  | SBlock (None, body) -> named_sblocks_in_stmts body.elt
  | If (_, b1, b2) ->
    named_sblocks_in_stmts b1.elt @ named_sblocks_in_stmts b2.elt
  | While (_, _, body) | For (_, _, _, body) -> named_sblocks_in_stmts body.elt
  | Commute (_, _, blocks, _, _) ->
    List.concat_map (fun b -> named_sblocks_in_stmts b.elt) blocks
  | _ -> []

let compute_inter_block_conflict_set
    (prog : prog)
    (safe_pos_map : (id * int list) list)
    : id list =
  let gcs =
    List.filter_map (function
      | Commutativity nodes -> Some nodes | _ -> None
    ) prog |> List.concat
  in
  let all_sblocks =
    List.filter_map (function
      | Gmdecl { elt = { body; _ }; _ } -> Some body.elt
      | _ -> None) prog
    |> List.concat_map named_sblocks_in_stmts
  in
  let blocks_by_label : (id * (exp node list option * stmt node list) list) list =
    List.fold_left (fun acc (label, params_opt, body) ->
      let existing = Option.value ~default:[] (List.assoc_opt label acc) in
      (label, (params_opt, body) :: existing) :: List.remove_assoc label acc
    ) [] all_sblocks
  in
  List.concat_map (fun gc ->
    let (groups, _, _, _) = gc.elt in
    let all_labels_in_gc = List.concat groups |> List.map fst |> List.sort_uniq compare in
    let multi_instance_labels =
      List.filter (fun label ->
        let count = List.length (List.filter (fun g -> List.exists (fun (l,_) -> l = label) g) groups) in
        count > 1
      ) all_labels_in_gc
    in
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
      let has_multiple = List.length labels_writing >= 2 in
      let has_multi_instance =
        List.exists (fun l -> List.mem l multi_instance_labels) labels_writing in
      if has_multiple || has_multi_instance then Some v else None
    ) var_to_labels
  ) gcs
  |> List.sort_uniq compare

(* ---- Post-DSWP: inter-task conflict set from the task graph ---- *)

(* Successors of task tid in the task dependency DAG *)
let task_successors (tasks : dswp_task list) (tid : dswp_taskid) : dswp_taskid list =
  match List.find_opt (fun t -> t.id = tid) tasks with
  | None -> []
  | Some t -> List.map (fun d -> d.pred_task) t.deps_out

(* Set of task IDs reachable from `start` following successor edges *)
let reachable_from (tasks : dswp_task list) (start : dswp_taskid) : dswp_taskid list =
  let rec bfs visited = function
    | [] -> visited
    | tid :: rest ->
      if List.mem tid visited then bfs visited rest
      else bfs (tid :: visited) (task_successors tasks tid @ rest)
  in
  bfs [] [start]

(* All pairs of tasks with no directed path between them — they run concurrently *)
let concurrent_task_pairs (tasks : dswp_task list) : (dswp_task * dswp_task) list =
  let reach = List.map (fun t -> (t.id, reachable_from tasks t.id)) tasks in
  List.concat_map (fun t1 ->
    let r1 = List.assoc t1.id reach in
    List.filter_map (fun t2 ->
      if t1.id >= t2.id then None
      else
        let r2 = List.assoc t2.id reach in
        if not (List.mem t2.id r1) && not (List.mem t1.id r2)
        then Some (t1, t2)
        else None
    ) tasks
  ) tasks

(* Variables that could race between concurrent task pairs.
   Uses conservative empty safe_args at the task level (no per-task
   commutativity condition is available here; NCB-level safe_args are
   handled separately via compute_inter_block_conflict_set). *)
let inter_task_conflict_set (tasks : dswp_task list) : id list =
  let pairs = concurrent_task_pairs tasks in
  List.concat_map (fun (t1, t2) ->
    let outer1 = outer_vars_of_block t1.body.elt in
    let outer2 = outer_vars_of_block t2.body.elt in
    let writes1 = conflicting_writes_in_stmts outer1 [] t1.body.elt in
    let writes2 = conflicting_writes_in_stmts outer2 [] t2.body.elt in
    let access1 = ids_in_stmts t1.body.elt |> List.sort_uniq compare in
    let access2 = ids_in_stmts t2.body.elt |> List.sort_uniq compare in
    List.filter (fun v -> List.mem v access2) writes1 @
    List.filter (fun v -> List.mem v access1) writes2
    |> List.sort_uniq compare
  ) pairs
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

(* Transform a block body: group conflicting writes under shared locks and
   recurse into all nested structures, including named SBlock bodies.
   `safe_pos_map` carries the NCB commutativity safe-position map so that
   named SBlocks can be recursed into with their own per-block safe_args.
   `safe_args` is the safe argument set for the CURRENT scope ([] at the
   top of a method body or task body; the block's own args inside a named
   SBlock). *)
let rec transform_stmts
    (conflict_set : id list)
    (safe_pos_map : (id * int list) list)
    (safe_args    : id list)
    (lock_st      : lock_state)
    (stmts        : stmt node list)
    : stmt node list =
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
  let rec group rev_acc pending_var pending_rev_group = function
    | [] ->
      let rev_acc = flush rev_acc pending_var pending_rev_group in
      List.rev rev_acc
    | (stmt, var_opt) :: rest ->
      (match var_opt with
      | None ->
        let rev_acc = flush rev_acc pending_var pending_rev_group in
        let t = transform_single conflict_set safe_pos_map safe_args lock_st stmt in
        group (t :: rev_acc) "" [] rest
      | Some v ->
        let (rev_acc', read_ext) =
          if pending_var = "" then
            match rev_acc with
            | prev :: rest_acc when stmt_reads_var v prev.elt ->
              (rest_acc, [prev])
            | _ -> (rev_acc, [])
          else (rev_acc, [])
        in
        if pending_var = v then
          group rev_acc' v (stmt :: (read_ext @ pending_rev_group)) rest
        else begin
          let rev_acc' = flush rev_acc' pending_var pending_rev_group in
          group rev_acc' v (stmt :: read_ext) rest
        end)
  and flush rev_acc pvar rev_group =
    match rev_group with
    | [] -> rev_acc
    | _ ->
      let lock_id = get_lock lock_st pvar in
      let group_stmts =
        List.rev_map (transform_single conflict_set safe_pos_map safe_args lock_st) rev_group
      in
      let wrapped = wrap_with_lock lock_id group_stmts in
      List.rev_append wrapped rev_acc
  in
  group [] "" [] annotated

(* Recurse into nested control structures.
   Named SBlocks are now handled here rather than delegated upward:
   each block is recursed into using its own per-label safe_args (from
   safe_pos_map), enabling both pre-DSWP (program bodies) and post-DSWP
   (task bodies) to share one traversal function. *)
and transform_single
    (conflict_set : id list)
    (safe_pos_map : (id * int list) list)
    (safe_args    : id list)
    (lock_st      : lock_state)
    (stmt         : stmt node)
    : stmt node =
  let elt' = match stmt.elt with
  | If (cond, b1, b2) ->
    if if_is_check_then_update conflict_set safe_args cond b1 b2 <> [] then stmt.elt
    else
      let b1' = { b1 with elt = transform_stmts conflict_set safe_pos_map safe_args lock_st b1.elt } in
      let b2' = { b2 with elt = transform_stmts conflict_set safe_pos_map safe_args lock_st b2.elt } in
      If (cond, b1', b2')
  | While (cond, inv, body) ->
    While (cond, inv, { body with elt = transform_stmts conflict_set safe_pos_map safe_args lock_st body.elt })
  | For (decls, eo, so, body) ->
    For (decls, eo, so, { body with elt = transform_stmts conflict_set safe_pos_map safe_args lock_st body.elt })
  | SBlock (None, body) ->
    SBlock (None, { body with elt = transform_stmts conflict_set safe_pos_map safe_args lock_st body.elt })
  | SBlock (Some (label, params_opt), body) ->
    if block_has_mutex body.elt then stmt.elt
    else
      (* Recurse into named SBlock body using the block's own safe_args *)
      let safe_pos      = Option.value ~default:[] (List.assoc_opt label safe_pos_map) in
      let block_sa      = match params_opt with
        | Some ps -> safe_arg_names ps safe_pos | None -> []
      in
      let body' = { body with elt =
        transform_stmts conflict_set safe_pos_map block_sa lock_st body.elt
      } in
      SBlock (Some (label, params_opt), body')
  | Commute (var, phi, blocks, pre, post) ->
    let blocks' = List.map (fun b ->
      { b with elt = transform_stmts conflict_set safe_pos_map safe_args lock_st b.elt }) blocks in
    Commute (var, phi, blocks', pre, post)
  | other -> other
  in
  { stmt with elt = elt' }

(* ---- Verbose helpers ---- *)

let print_lock_state (lock_st : lock_state) =
  let sorted = List.sort (fun (_, a) (_, b) -> compare a b) lock_st.var_to_lock in
  List.iter (fun (var, id) ->
    Servois2.Util.pfvv "    lock %d <- variable \"%s\"\n" id var
  ) sorted

(* ---- Pre-DSWP entry point ---- *)

(* Transform all method bodies in the program, locking NCB-level conflicts.
   Works on the source AST before DSWP decomposition. *)
let transform_prog (prog : prog) : prog =
  let safe_pos_map  = build_safe_pos_map prog in
  let conflict_set  = compute_inter_block_conflict_set prog safe_pos_map in
  if conflict_set = [] then prog
  else begin
    let lock_st = create_lock_state () in
    let result = List.map (function
      | Gmdecl decl ->
        let body' = { decl.elt.body with elt =
          transform_stmts conflict_set safe_pos_map [] lock_st decl.elt.body.elt
        } in
        Gmdecl { decl with elt = { decl.elt with body = body' } }
      | other -> other
    ) prog in
    Servois2.Util.pfvv "[lock synthesis] pre-DSWP\n";
    Servois2.Util.pfvv "  conflict set: {%s}\n" (String.concat ", " conflict_set);
    let method_names = List.filter_map (function
      | Gmdecl decl -> Some decl.elt.mname | _ -> None) prog in
    Servois2.Util.pfvv "  methods instrumented: %s\n" (String.concat ", " method_names);
    Servois2.Util.pfvv "  locks synthesized:\n";
    print_lock_state lock_st;
    result
  end

(* ---- Post-DSWP entry point ---- *)

(* Transform task bodies after DSWP decomposition, locking both:
   (a) inter-task conflicts — globals written by concurrent DSWP tasks;
   (b) NCB intra-task conflicts — globals shared between concurrent NCB
       instances within a single task.
   A single shared lock_state ensures the same variable always gets the
   same lock ID across all tasks. *)
let synthesize_tasks (prog : prog) (tasks : dswp_task list) : dswp_task list =
  let safe_pos_map  = build_safe_pos_map prog in
  let inter_set     = inter_task_conflict_set tasks in
  let intra_set     = compute_inter_block_conflict_set prog safe_pos_map in
  let conflict_set  = List.sort_uniq compare (inter_set @ intra_set) in
  if conflict_set = [] then tasks
  else begin
    let lock_st = create_lock_state () in
    let instrumented = ref [] in
    let result = List.map (fun task ->
      if block_has_mutex task.body.elt then task
      else begin
        instrumented := task.id :: !instrumented;
        let body' = { task.body with elt =
          transform_stmts conflict_set safe_pos_map [] lock_st task.body.elt
        } in
        { task with body = body' }
      end
    ) tasks in
    Servois2.Util.pfvv "[lock synthesis] post-DSWP\n";
    Servois2.Util.pfvv "  inter-task conflict set: {%s}\n" (String.concat ", " inter_set);
    Servois2.Util.pfvv "  intra-task conflict set: {%s}\n" (String.concat ", " intra_set);
    Servois2.Util.pfvv "  tasks instrumented: %s\n"
      (String.concat ", " (List.map string_of_int (List.rev !instrumented)));
    Servois2.Util.pfvv "  locks synthesized:\n";
    print_lock_state lock_st;
    result
  end
