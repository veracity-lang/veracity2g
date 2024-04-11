open Ast 
open Ast_print
open Format
open Range
open Util

type dependency =
| ControlDep
| DataDep of id list
| Commute of bool
| Disjoint

type enode_ast_elt = 
| Entry 
| EWhile of exp node
| EIf of exp node
| EIfElse of exp node
| EFor of vdecl list * exp node option * stmt node option
| EStmt of stmt node

let transform_stmt (s: stmt node) : enode_ast_elt = 
  match s.elt with 
  | If (e, b1, b2) ->
    begin match b2.elt with
    | [] -> EIf e
    | _ -> EIfElse e
    end
  | While (e,_) -> EWhile e 
  | For (v,e,s,_) -> EFor (v,e,s)
  | _ -> EStmt s

type pdg_node = {
  l: Range.t; 
  n: enode_ast_elt;
  src: stmt node option 
}

type pdg_edge = {
  src : pdg_node;
  dst : pdg_node;
  dep : dependency;
  loop_carried : bool
}

type exe_pdg = {
  entry_node: pdg_node option;
  nodes : pdg_node list;
  edges : pdg_edge list;
}

let empty_exe_pdg () : exe_pdg =
  { entry_node = None; nodes = []; edges = [] }

let add_node (pdg : exe_pdg) (s : stmt node) : pdg_node * exe_pdg =
  let n = {l = s.loc; n = transform_stmt s; src = Some s} in 
  n, { pdg with nodes = pdg.nodes @ [n] }

let add_edge (pdg : exe_pdg) (src : pdg_node) (dst : pdg_node) dep : exe_pdg = 
  { pdg with edges = pdg.edges @ [{ src; dst; dep; loop_carried = false }] }


let string_of_dep = function
  | ControlDep -> "ControlDep"
  | DataDep vars -> sp "DataDep (%s)" (AstML.string_of_list (fun s -> s) vars) 
  | Commute b -> sp "Commute (%s)" (Bool.to_string b)
  | Disjoint -> "Disjoint"


let c_of_stmt = function
  | Entry -> "Entry"
  | EWhile e -> sp "while(%s)" (Ast_to_c.c_of_expnode e)
  | EIf e -> sp "if(%s)" (Ast_to_c.c_of_expnode e) 
  | EIfElse e -> sp "if(%s)" (Ast_to_c.c_of_expnode e) 
  | EFor(inits, e, update) -> sp "for(%s; %s; %s)" (String.concat ", " @@ List.map (fun (id, (ty, rhs)) -> sp "%s %s = %s" (Ast_to_c.c_of_ty ty) (!Ast_to_c.mangle id) (Ast_to_c.c_of_expnode rhs)) inits) (e |> Option.map Ast_to_c.c_of_expnode |> Option.value ~default:"") (update |> Option.map Ast_to_c.c_of_stmtnode |> Option.value ~default:"")
  | EStmt s -> Ast_to_c.c_of_stmt s.elt
  
let string_of_pdg_node_stmt s =
  (* let big_string = Ast_to_c.c_of_stmt s in  *)
  (* if String.length big_string > 20 then String.sub big_string 0 19 else big_string *)
  c_of_stmt s


let print_pdg pdg fn : unit = 
  let oc = open_out fn in
  output_string oc (String.concat "\n" [
    "pdg G {\n";
    (* Styles *)
    "  pdg [rankdir=\"TB\", fontsize=20, label=\"Black=CFG, Red=ControlDep, Blue=DataDep\", labelloc=t]";
    "  node [shape=box, style=\"rounded,filled\", fontname=\"Courier\", margin=0.05]";
    "  pdg_edge [arrowhead=vee, arrowsize=1, fontname=\"Courier\"]";
    (* Nodes *)
    (* let s = "\" [label=\""^(match pdg.entry_node with | Some en -> string_of_pdg_node_stmt en.n)^"\"];\n" in *)
    List.fold_left (fun acc node -> acc ^ "\"" ^ (Range.string_of_range_nofn node.l)
    ^ "\" [label=\""^(string_of_pdg_node_stmt node.n)^"\"];\n") "" pdg.nodes;
    (* edges *)
    List.fold_left (fun acc e -> acc ^ (match e.dep with
       | DataDep idlist ->
           let ids = String.concat "," idlist in
          "\"" ^ (Range.string_of_range_nofn e.src.l) ^ "\" -> \"" 
                ^ (Range.string_of_range_nofn e.dst.l) ^ "\" "
                ^ "[style=solid, color=green, label=\""^ids^"\"];\n" 
       | Commute _  
       | Disjoint 
       | ControlDep ->
          "\"" ^ (Range.string_of_range_nofn e.src.l) ^ "\" -> \"" 
               ^ (Range.string_of_range_nofn e.dst.l) ^ "\" "
               ^ "[style=dashed, color=maroon];\n" (*label=\""^(string_of_dep e.dep)^"\"];\n"*)
    )) "" pdg.edges;
    "}\n";
  ]);
  print_endline ("pdg written to " ^ fn);
  close_out oc


let print_pdg_debug pdg =
  match pdg.entry_node with | Some en -> Printf.printf "entry node: %s\n" (Range.string_of_range en.l);
  List.iteri (fun i s -> Printf.printf "node %d: %s\n" i (Range.string_of_range s.l)) pdg.nodes;
  List.iteri (fun i e -> Printf.printf "pdg_edge %d (%s) - %b: %s - %s\n" i (string_of_dep e.dep) e.loop_carried (Range.string_of_range_nofn e.src.l) (Range.string_of_range_nofn e.dst.l)) pdg.edges


let find_node (s: stmt node) pdg : pdg_node =
    let sl = s.loc in 
    List.find (
        fun {l=loc;n} -> String.equal (Range.string_of_range loc) (Range.string_of_range sl) 
    ) pdg.nodes

let rvalue = 1
let lvalue = 0

let set_vars_side (vars : string list) side : (string * int) list = 
  List.map (fun v -> (v, side)) vars

let rec find_block_vars block : (string * int) list = 
  match block with 
  | [] -> []
  | stmt::tl -> (find_stmt_vars stmt) @ (find_block_vars tl)

and find_stmt_vars (stmt: enode_ast_elt) : (string * int) list = 
  match stmt with
  | EWhile e | EIf e | EIfElse e  -> set_vars_side (find_exp_vars e) rvalue
  (* | EFor (vdecls, eoption, soption) ->  *)
  | EStmt s ->
    begin match s.elt with 
    | Assn (e1,e2) -> (set_vars_side (find_exp_vars e1) lvalue) @ (set_vars_side (find_exp_vars e2) rvalue)
    | Decl vdecl ->
      let id, (_, e) = vdecl in (id, lvalue) :: (set_vars_side (find_exp_vars e) rvalue)
    | Ret (Some e) -> set_vars_side (find_exp_vars e) rvalue
    | _ -> []
    end 
  | Entry -> []

  (* 
  | SCallRaw of id * exp node list
  | SCall of method_variant * exp node list
  | Raise of exp node
  | Commute of commute_variant * commute_condition * block node list
  | Assert of exp node
  | Assume of exp node
  | Havoc of id
  | Require of exp node
  | SBlock of blocklabel option * block node
  | GCommute of commute_variant * commute_condition * commute_pre_cond * block node list * commute_post_cond *)

and find_exp_vars exp : string list =
  match exp.elt with 
  | CStr s | Id s -> [s]
  | CArr (_, expl) -> List.concat_map find_exp_vars expl
  | NewArr (_, e) | Uop (_, e) -> find_exp_vars e
  | Index (e1, e2) | Bop (_, e1, e2) -> (find_exp_vars e1) @ (find_exp_vars e2) 
  | CallRaw (_, expl) -> List.concat_map find_exp_vars expl
  | Call (m, expl) -> List.concat_map find_exp_vars expl (* TODO: check *)
  | Ternary (e1, e2, e3) -> (find_exp_vars e1) @ (find_exp_vars e2) @ (find_exp_vars e3)
  | _ -> []
  (* 
  | CStruct of id * exp node bindlist
  | Proj of exp node * id *)

let src_to_dst = 1
let dst_to_src = 0

let has_data_dep src dst : bool * string list * int =
  let list1 = find_stmt_vars src.n in 
  let list2 = find_stmt_vars dst.n in 
  let rec has_common_element list1 list2 vars : bool * string list * int = 
    match list1 with
    | [] -> false, vars, src_to_dst 
    | (head, val1) :: tail ->
      if List.mem_assoc head list2 then begin
        let val2 = List.assoc head list2 in 
        begin match val1, val2 with 
        | 0, 1 -> true, head :: vars, src_to_dst
        | 1, 0 -> true, head :: vars, dst_to_src
        | _, _ -> false, vars, src_to_dst
        end
      end
      else
        has_common_element tail list2 vars
  in has_common_element list1 list2 []


let rec apply_pairs f lst =
  match lst with
  | [] -> ()
  | x::xs -> List.iter (fun y -> f x y) xs; apply_pairs f xs

let add_dataDep_edges pdg = 
  let p = ref pdg in 
  apply_pairs (fun x y -> 
    let dep, vars, dir = has_data_dep x y in 
    if dep then begin
      if dir == 1 then 
        p := add_edge !p x y (DataDep vars)
      else 
        p := add_edge !p y x (DataDep vars)
    end
  ) pdg.nodes;
  !p


type visited = (pdg_node * bool) list

let rec mark_visited n visited =
  match visited with
  | [] -> visited
  | (node, _) :: rest ->
    if node = n then
      (node, true) :: rest
    else
      (node, false) :: mark_visited n rest

let compare_nodes n1 n2 = 
  String.equal (Range.string_of_range n1.l) (Range.string_of_range n2.l)

(* Function to check if a control dependence is loop-carried *)
(* let is_control_dependence_loop_carried (edge: pdg_edge) pdg =
  let rec has_loop_backedge_to_loop_header (n1: pdg_node) (n2: pdg_node) (edge: pdg_edge) (visited: visited) =
    let visited = mark_visited n1 visited in 
    match edge.dep with 
    | ControlDep -> 
      if compare_nodes n1 n2 then true
      else if List.assoc n2 visited then false
      else has_loop_backedge_to_loop_header n2 visited
    | _ -> false
  in
  let rec all_paths_contain_loop_backedge node1 node2 visited =
    visited.(node1.id) <- true;
    if node1.id = node2.id then true
    else begin
      match node1.control_dependence with
      | None -> false
      | Some pred ->
        if visited.(pred.id) then false
        else all_paths_contain_loop_backedge pred node2 visited
    end
  in
  has_loop_backedge_to_loop_header edge.src edge.dst edge (List.map (fun v -> (v, false)) pdg.nodes) &&
  all_paths_contain_loop_backedge n1 n2 (Array.make (Array.length nodes) false) *)


(* Function to check if a dependence arc is loop-carried *)
let is_loop_carried_dependence (pdg: exe_pdg) (edge: pdg_edge) =
  let n1 = edge.src in
  let n2 = edge.dst in
  let is_loop_header node = 
    match node.n with 
    | EFor _ | EWhile _ -> true
    | _ -> false
  in
  match edge.dep with
  | DataDep register ->
    (* Check if the definition of the register reaches the loop header *)
    let rec definition_reaches_loop_header (node: pdg_node) (visited: visited ref) =
      if List.assoc node !visited then false
      else begin
        visited := mark_visited node !visited;
        if is_loop_header node then true 
        else
          match List.find_opt (fun e -> compare_nodes e.dst node) pdg.edges with
          | None -> false
          | Some e -> definition_reaches_loop_header e.src visited
      end
    in
    let visited = ref @@ List.map (fun v -> (v, false)) (pdg.nodes) in
    let definition_reaches_loop_header = definition_reaches_loop_header n1 visited in
    (* Check if there is an upwards-exposed use of the register in n2 at the loop header *)
    let upwards_exposed_use_in_loop_header =
      match List.find_opt (fun e -> is_loop_header e.dst) pdg.edges with
      | None -> false
      | Some loop_header_edge ->
        let rec has_upwards_exposed_use node =
          let uses, _ = List.split (List.filter (fun (v, side) -> side == rvalue) (find_stmt_vars node.n)) in 
          if List.exists (fun use -> List.mem use register) uses then true
          else match List.find_opt (fun e -> compare_nodes e.src node) pdg.edges with
            | None -> false
            | Some e ->
              if is_loop_header e.src then false (* Reached loop header *)
              else has_upwards_exposed_use e.src
        in
        has_upwards_exposed_use n2
    in
    definition_reaches_loop_header && upwards_exposed_use_in_loop_header
  | _ -> false (* Dependence is not through registers *)

(* Function to find loop-carried dependencies in the exe_pdg graph *)
let mark_loop_carried_dependencies pdg : exe_pdg =
  let nodes = match pdg.entry_node with | Some e -> e :: pdg.nodes | None -> pdg.nodes in
  let pdg_tmp = {pdg with nodes= nodes} in
  let e = List.map (fun edge -> if is_loop_carried_dependence pdg_tmp edge then {edge with loop_carried= true} else edge) pdg_tmp.edges
  in 
  {pdg with edges = e}


let build_pdg (block: block) entry_loc : exe_pdg = 
  let pdg = empty_exe_pdg() in 
  let pdg = { pdg with entry_node = Some {l= entry_loc; n= Entry; src= None} } in
  let rec traverse_ast block pdg : exe_pdg =
    match block with
    | [] -> pdg
    | stmt::tl ->
      let updated_pdg = begin match stmt.elt with 
      | If (e, blk1, blk2) ->
        let src, pdg = add_node pdg stmt in
        let pdg = traverse_ast blk2.elt (traverse_ast blk1.elt pdg) in 

        List.fold_left (fun pdg s -> add_edge pdg src (find_node s pdg) ControlDep) pdg blk1.elt
          
      | While (_, bl) | For (_, _, _, bl) ->
        let src, pdg = add_node pdg stmt in
        let pdg = traverse_ast bl.elt pdg in 

        let pdg = add_edge pdg src src ControlDep in
        List.fold_left (fun pdg s -> add_edge pdg src (find_node s pdg) ControlDep) pdg bl.elt

      (* | SBlock (blocklabel, bl) -> 
          let n = stmt in 
          snd (add_node pdg n) *)

      | _ -> 
        let n = stmt in 
        snd (add_node pdg n)
      end 
      in 
      traverse_ast tl updated_pdg
  in 
  let pdg = (traverse_ast block pdg) in
  (* add data dependency edges for each pairs of nodes *)
  let pdg = add_dataDep_edges pdg in 
  (* connect the entry node to the header nodes *)
  let pdg = begin match pdg.entry_node with 
  | Some en -> List.fold_left (fun pdg s -> let n = find_node s pdg in add_edge pdg en n ControlDep) pdg block
  | None -> pdg
  end
  in
  mark_loop_carried_dependencies pdg

let find_neighbors pdg node : pdg_node list = 
  List.fold_left (fun neighbors e -> if compare_nodes e.src node then neighbors @ [e.dst] else neighbors) [] pdg.edges

let rec dfs_util pdg (curr: pdg_node) (visited: visited ref) : pdg_node list =
  visited := List.remove_assoc curr !visited @ [(curr, true)]; 
  let neighbors = find_neighbors pdg curr in 
  List.fold_left (fun r n -> if not (List.assoc n !visited) then r @ (dfs_util pdg n visited) else r) [curr] neighbors

let transpose pdg : exe_pdg =
  {pdg with edges = List.map (fun {src=s; dst=d; dep=dp; loop_carried=l} -> {src=d; dst=s; dep=dp; loop_carried=l}) pdg.edges}

let rec fill_order pdg (curr: pdg_node) (visited: visited ref) stack =
  visited := List.remove_assoc curr !visited @ [(curr, true)]; 
  let neighbors = find_neighbors pdg curr in 
  List.iter (fun n -> if not (List.assoc n !visited) then fill_order pdg n visited stack) neighbors;
  Stack.push curr stack

let find_sccs pdg : pdg_node list list =
  let stack = Stack.create () in
  let nodes = match pdg.entry_node with | Some e -> e :: pdg.nodes | None -> pdg.nodes in
  let pdg = {pdg with nodes= nodes} in
  let visited = ref @@ List.map (fun v -> (v, false)) pdg.nodes in 
  List.iter (fun n -> if not (List.assoc n !visited) then fill_order pdg n visited stack) pdg.nodes;
  let reversed_pdg = transpose pdg in
  let visited = ref @@ List.map (fun v -> (v, false)) pdg.nodes in 
  let sccs = ref [] in 
  while not (Stack.is_empty stack) do
    let s = Stack.pop stack in
    if not (List. assoc s !visited) then begin
      sccs := !sccs @ [dfs_util reversed_pdg s visited];
    end
  done;
  !sccs

let print_sccs (sccs: pdg_node list list) =
  List.iter (fun s -> List.iter (fun c -> Printf.printf "%s " (Range.string_of_range_nofn c.l)) s; print_newline ()) sccs

type dag_node_label = Doall | Sequential

type dag_node = {
  n : pdg_node list;
  label: dag_node_label
}

type dag_edge = {
  dag_src : dag_node;
  dag_dst : dag_node;
  dep : dependency;
  loop_carried : bool
}

type dag_scc = {
  entry_node: pdg_node option;
  nodes : dag_node list;
  edges : dag_edge list;
}

let id_of_dag_node (dn:dag_node) : string = 
  List.fold_left (fun acc pdgnode -> acc ^ "_" ^ (Range.string_of_range_nofn pdgnode.l)) "" dn.n

let dag_pdgnode_to_string (pdgnodes:pdg_node list) : string = 
  List.fold_left (fun acc pnode -> acc ^ (Range.string_of_range_nofn pnode.l)
  ^ ":"^(string_of_pdg_node_stmt pnode.n) ^ ",") "" pdgnodes

let color_of_dagnode = function
  | Doall -> "white"
  | Sequential -> "gray"

let print_dag (d:dag_scc) fn node_to_string_fn : unit = 
  let oc = open_out fn in
  output_string oc (String.concat "\n" [
    "digraph G {";
    (* Styles *)
    "  node [shape=box, style=\"rounded,filled\", fontname=\"Courier\", margin=0.05]";
    "  edge [arrowhead=vee, arrowsize=1, fontname=\"Courier\"]";
    (* Nodes *)
    List.fold_left (fun acc node -> acc ^ "\"" ^ (id_of_dag_node node)
    ^ "\" [color=\""^(color_of_dagnode node.label)^"\" label=\""^(node_to_string_fn node.n)^"\"];\n") "" d.nodes;
    (* edges *)
    List.fold_left (fun acc e -> acc ^ (match e.dep with
       | DataDep idlist ->
           let ids = String.concat "," idlist in
          "\"" ^ (id_of_dag_node e.dag_src) ^ "\" -> \"" 
                ^ (id_of_dag_node e.dag_dst) ^ "\" "
                ^ "[style=solid, color=green, label=\""^ids^"\"];\n" 
       | Commute _  
       | Disjoint 
       | ControlDep ->
          "\"" ^ (id_of_dag_node e.dag_src) ^ "\" -> \"" 
               ^ (id_of_dag_node e.dag_dst) ^ "\" "
               ^ "[style=dashed, color=maroon];\n" (*label=\""^(string_of_dep e.dep)^"\"];\n"*)
    )) "" d.edges;
    "}\n";
  ]);
  print_endline ("dag written to " ^ fn);
  close_out oc

let coalesce_sccs (pdg: exe_pdg) (sccs: pdg_node list list) : dag_scc =
  let nodes = List.map (fun scc -> {n= scc; label= Sequential}) sccs in
  let find_node_scc n scc =
    List.mem n scc
  in
  let find_dag_node (sub_node : pdg_node) =
    List.find (fun node -> List.exists (fun e -> compare_nodes e sub_node) node.n) nodes
  in
  let is_scc (n1: pdg_node) (n2: pdg_node) : bool =
    List.exists (fun scc -> find_node_scc n1 scc && find_node_scc n2 scc) sccs 
  in

  let filtered_edges = List.filter (fun {src= s; dst= d; _} -> not (is_scc s d)) pdg.edges in 
  let edges = List.map (
    fun {src= s; dst= d; dep=dp; loop_carried =l} -> 
    {dag_src= find_dag_node s; dag_dst= find_dag_node d; dep=dp; loop_carried=l}
  ) filtered_edges in 
  {entry_node = pdg.entry_node; nodes; edges}


let string_of_dag_label = function
  | Doall -> "doall"
  | Sequential -> "sequential"


let print_dag_debug dag_scc =
  match dag_scc.entry_node with | Some en -> Printf.printf "entry node: %s\n" (Range.string_of_range_nofn en.l);
  let string_of_node n = List.fold_left (fun acc s -> acc ^ (Range.string_of_range_nofn s.l) ^ " ") "" n in 
  List.iteri (fun i sl -> Printf.printf "node %d (%s): %s" i (string_of_dag_label sl.label) (string_of_node sl.n); print_newline()) dag_scc.nodes;
  List.iteri (fun i e -> Printf.printf "pdg_edge %d (%s) - %b: %s - %s\n" i (string_of_dep e.dep) e.loop_carried (string_of_node e.dag_src.n) (string_of_node e.dag_dst.n)) dag_scc.edges



(* let thread_partitioning (dag_scc: dag_scc) (threads: thread list): assignment =
  let initial_partition = List.map (fun node -> [node]) (topological_sort dag_scc) in
  let classify_block (block: block) = if List.exists is_doall_node block then `Doall else `Sequential in
  let partition_with_labels = List.map (fun block -> (block, classify_block block)) initial_partition in
  let partition = merge_doall_blocks (List.map fst partition_with_labels) in
  let maxd_block = max_profile_weight_block partition in
  let partition = List.map (fun block -> if block = maxd_block then `Doall else `Sequential) partition in
  let seq_partition = merge_sequential_blocks (List.filter (fun (_, label) -> label = `Sequential) partition) in
  let doall_partition = List.filter (fun (_, label) -> label = `Doall) partition in
  let d = List.length threads - List.length seq_partition in
  let doall_threads, sequential_threads = List.split_at d threads in

  let rec assign_blocks blocks threads assignment =
    match blocks, threads with
    | block :: rest_blocks, th :: rest_threads ->
      if snd block = `Sequential then
        assign_blocks rest_blocks rest_threads ((fst block, [th]) :: assignment)
      else
        ((fst block, doall_threads) :: assignment)
    | [], _ -> List.rev assignment
    | _ -> failwith "Not enough threads for assignment"
  in

  assign_blocks partition_with_labels sequential_threads [] *)


let ps_dswp (body: block node) loc = 
  let pdg = build_pdg body.elt loc in 
  print_pdg_debug pdg;
  print_pdg pdg "/tmp/pdg.dot";
  let sccs = find_sccs pdg in
  Printf.printf "Strongly Connected Components:\n";
  print_sccs sccs;
  let dag_scc = coalesce_sccs pdg sccs in
  print_dag_debug dag_scc;
  print_dag dag_scc "/tmp/dag-scc.dot" dag_pdgnode_to_string;
  ()
  (* print_pdg dag_scc "/tmp/dag.dot" *)