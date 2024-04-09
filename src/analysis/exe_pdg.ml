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

type enode = {
  l: Range.t; 
  n: enode_ast_elt 
}

type edge = {
  src : enode;
  dst : enode;
  dep : dependency;
}

type exe_pdg = {
  entry_node: enode option;
  nodes : enode list;
  edges : edge list;
}

let empty_exe_pdg () : exe_pdg =
  { entry_node = None; nodes = []; edges = [] }

let add_node (pdg : exe_pdg) (s : stmt node) : enode * exe_pdg =
  let n = {l = s.loc; n = transform_stmt s} in 
  n, { pdg with nodes = pdg.nodes @ [n] }

let add_edge (pdg : exe_pdg) (src : enode) (dst : enode) dep : exe_pdg = 
  { pdg with edges = pdg.edges @ [{ src; dst; dep }] }


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
    "  edge [arrowhead=vee, arrowsize=1, fontname=\"Courier\"]";
    (* Nodes *)
    (* let s = "\" [label=\""^(match pdg.entry_node with | Some en -> string_of_pdg_node_stmt en.n)^"\"];\n" in *)
    List.fold_left (fun acc node -> acc ^ "\"" ^ (Range.string_of_range_nofn node.l)
    ^ "\" [label=\""^(string_of_pdg_node_stmt node.n)^"\"];\n") "" pdg.nodes;
    (* Edges *)
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
  List.iteri (fun i -> fun s -> Printf.printf "node %d: %s\n" i (Range.string_of_range s.l)) pdg.nodes;
  List.iteri (fun i -> fun e -> Printf.printf "edge %d (%s): %s - %s\n" i (string_of_dep e.dep) (Range.string_of_range e.src.l) (Range.string_of_range e.dst.l)) pdg.edges


let find_node (s: stmt node) pdg : enode =
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
  apply_pairs (fun x -> fun y -> 
    let dep, vars, dir = has_data_dep x y in 
    if dep then begin
      if dir == 1 then 
        p := add_edge !p x y (DataDep vars)
      else 
        p := add_edge !p y x (DataDep vars)
    end
  ) pdg.nodes;
  !p

let build_pdg (block: block) entry_loc : exe_pdg = 
  let pdg = empty_exe_pdg() in 
  let pdg = { pdg with entry_node = Some {l= entry_loc; n= Entry} } in
  let rec traverse_ast block pdg : exe_pdg =
    match block with
    | [] -> pdg
    | stmt::tl ->
      let updated_pdg = begin match stmt.elt with 
      | If (e, blk1, blk2) ->
        let src, pdg = add_node pdg stmt in
        let pdg = traverse_ast blk2.elt (traverse_ast blk1.elt pdg) in 

        List.fold_left (fun pdg -> fun s -> add_edge pdg src (find_node s pdg) ControlDep) pdg blk1.elt
          
      | While (_, bl) | For (_, _, _, bl) ->
        let src, pdg = add_node pdg stmt in
        let pdg = traverse_ast bl.elt pdg in 

        let pdg = add_edge pdg src src ControlDep in
        List.fold_left (fun pdg -> fun s -> add_edge pdg src (find_node s pdg) ControlDep) pdg bl.elt

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
  begin match pdg.entry_node with 
  | Some en -> List.fold_left (fun pdg -> fun s -> let n = find_node s pdg in add_edge pdg en n ControlDep) pdg block
  | None -> pdg
  end



(* Strongly connected components using BFS *)

(* Define types for directed pdg and DFS traversal *)
(* type 'a pdg = ('a * 'a list) list *)
type visited = (enode * bool) list

let compare_nodes n1 n2 = 
  String.equal (Range.string_of_range n1.l) (Range.string_of_range n2.l)

let find_neighbors pdg node : enode list = 
  List.fold_left (fun neighbors -> fun e -> if compare_nodes e.src node then neighbors @ [e.dst] else neighbors) [] pdg.edges
(* 
(* Depth-first search on a directed pdg *)
let rec dfs (pdg: exe_pdg) (visited: visited) (v: enode) (stack: enode list) : enode list =
  Printf.printf "DFS: %s - %b\n" (Range.string_of_range_nofn v.l) (List.assoc v visited);
  if List.assoc v visited then
    stack
  else
    let neighbors = find_neighbors pdg v in
    List.iter (fun n -> Printf.printf "nnn: %s\n" (Range.string_of_range_nofn n.l)) neighbors;
    let new_stack = v :: stack in
    let new_visited = (v, true) :: visited in
    List.fold_left (fun s -> fun v -> dfs pdg new_visited v s) new_stack neighbors

(* Reverse the directed pdg *)
let rec reverse_pdg pdg : exe_pdg =
  {pdg with edges = List.map (fun {src=s; dst=d; dep=dp} -> {src=d; dst=s; dep=dp}) pdg.edges}
  (* let add_edge_pdg (v, neighbors) acc =
    let add_to_neighbor acc' n = 
      let updated = 
        match List.assoc_opt n acc' with
        | Some l -> (n :: l)
        | None -> [n]
      in
      (n, updated) :: acc'
    in
    List.fold_left add_to_neighbor acc neighbors
  in
  List.fold_left (fun n -> fun v -> add_edge_pdg v n) [] pdg *)

(* Main function to find strongly connected components in a directed pdg *)
let scc_pdg (pdg: exe_pdg) : enode list list =
  let rec first_pass (nodes: enode list) (stack: enode list) (visited: visited) : enode list =
    match nodes with
    | [] -> stack
    | v :: tl ->
      if List.assoc v visited then
        first_pass tl stack visited
      else
        let new_stack = dfs pdg visited v stack in
        first_pass tl new_stack visited
  in
  let rec second_pass (pdg: exe_pdg) (stack: enode list) (visited: visited) : enode list list =
    match stack with
    | [] -> []
    | v :: tl ->
      if List.assoc v visited then
        second_pass pdg tl visited
      else
        let scc_group = dfs pdg visited v [] in
        scc_group :: second_pass pdg tl visited
  in
  let reversed_pdg = reverse_pdg pdg in
  let nodes = match pdg.entry_node with | Some e -> e :: pdg.nodes | None -> pdg.nodes in 
  let visited = List.map (fun v -> (v, false)) nodes in
  let stack = first_pass nodes [] visited in
  List.iter (fun n -> Printf.printf "n: %s\n" (Range.string_of_range_nofn n.l)) stack;
  second_pass reversed_pdg stack visited

let print_sccs pdg =
  let sccs = scc_pdg pdg in
  Printf.printf "size: %d\n" (List.length sccs);
  List.iteri (fun i -> fun scc -> Printf.printf "%d: [ %s ]\n" i (String.concat "; " (List.map (fun s -> Range.string_of_range_nofn s.l) scc))) sccs 
   *)



(*** *)

let rec dfs_util pdg (curr: enode) (visited: visited ref) : enode list =
  visited := List.remove_assoc curr !visited @ [(curr, true)]; 
  let neighbors = find_neighbors pdg curr in 
  List.fold_left (fun r-> fun n -> if not (List.assoc n !visited) then r @ (dfs_util pdg n visited) else r) [curr] neighbors

let transpose pdg : exe_pdg =
  {pdg with edges = List.map (fun {src=s; dst=d; dep=dp} -> {src=d; dst=s; dep=dp}) pdg.edges}

let rec fill_order pdg (curr: enode) (visited: visited ref) stack =
  visited := List.remove_assoc curr !visited @ [(curr, true)]; 
  let neighbors = find_neighbors pdg curr in 
  List.iter (fun n -> if not (List.assoc n !visited) then fill_order pdg n visited stack) neighbors;
  Stack.push curr stack

let find_sccs pdg : enode list list =
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

let print_sccs (sccs: enode list list) =
  List.iter (fun s -> List.iter (fun c -> Printf.printf "%s " (Range.string_of_range_nofn c.l)) s; print_newline ()) sccs

let ps_dswp (body: block node) loc = 
  let pdg = build_pdg body.elt loc in 
  print_pdg_debug pdg;
  print_pdg pdg "/tmp/pdg.dot";
  let sccs = find_sccs pdg in
  Printf.printf "Strongly Connected Components:\n";
  print_sccs sccs