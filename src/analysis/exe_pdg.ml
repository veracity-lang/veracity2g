open Ast 
open Ast_print
open Format
open Range
open Util

type dependency =
(* | ProgramOrder *)
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
  (* let big_string = 
    begin match s with 
    | Entry -> "Entry"
    | EWhile e -> sp "EWhile (%s)" (AstML.string_of_exp e)
    | EIf e -> sp "EIf (%s)" (AstML.string_of_exp e)
    | EIfElse e  -> sp "EIfElse (%s)" (AstML.string_of_exp e)
    | EFor (d,e,s) -> sp "EFor (%s, %s, %s)"
                          (AstML.string_of_list AstML.string_of_vdecl_aux d) 
                          (AstML.string_of_option AstML.string_of_exp e)
                          (AstML.string_of_option AstML.string_of_stmt s)
    | EStmt s -> AstML.string_of_stmt s 
      end  
  in  *)

  (* let big_string = Ast_to_c.c_of_stmt s in  *)
  (* if String.length big_string > 20 then String.sub big_string 0 19 else big_string *)

  c_of_stmt s


let print_pdg pdg fn : unit = 
  let oc = open_out fn in
  output_string oc (String.concat "\n" [
    "digraph G {\n";
    (* Styles *)
    "  graph [rankdir=\"TB\", fontsize=20, label=\"Black=CFG, Red=ControlDep, Blue=DataDep\", labelloc=t]";
    "  node [shape=box, style=\"rounded,filled\", fontname=\"Courier\", margin=0.05]";
    "  edge [arrowhead=vee, arrowsize=1, fontname=\"Courier\"]";
    (* Nodes *)
    (* let s = "\" [label=\""^(match pdg.entry_node with | Some en -> string_of_pdg_node_stmt en.n)^"\"];\n" in *)
    List.fold_left (fun acc node -> acc ^ "\"" ^ (Range.string_of_range_nofn node.l)
    ^ "\" [label=\""^(string_of_pdg_node_stmt node.n)^"\"];\n") "" pdg.nodes;
    (* Edges *)
    List.fold_left (fun acc e -> acc ^ (match e.dep with
       | DataDep _ -> ""
       | Commute _  
       | Disjoint 
       | ControlDep ->
          "\"" ^ (Range.string_of_range_nofn e.src.l) ^ "\" -> \"" 
               ^ (Range.string_of_range_nofn e.dst.l) ^ "\" "
               ^ "[style=dashed];\n" (*label=\""^(string_of_dep e.dep)^"\"];\n"*)
    )) "" pdg.edges;
    "}\n";
  ]);
  print_endline ("Graph written to " ^ fn);
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


let rec find_block_vars block = 
  match block with 
  | [] -> []
  | stmt::tl -> (find_stmt_vars stmt) @ (find_block_vars tl)

and find_stmt_vars (stmt: enode_ast_elt) = 
  match stmt with
  | EWhile e | EIf e | EIfElse e  -> (find_exp_vars e)
  (* | EFor (vdecls, eoption, soption) ->  *)
  | EStmt s ->
    begin match s.elt with 
    | Assn (e1,e2) -> (find_exp_vars e1) @ (find_exp_vars e2) 
    | Decl vdecl ->
      let id, (_, e) = vdecl in id :: find_exp_vars e
    | Ret (Some e) -> (find_exp_vars e)
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

and find_exp_vars exp =
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

let has_data_dep src dst : bool * string list  =
  let list1 = find_stmt_vars src.n in 
  let list2 = find_stmt_vars dst.n in 
  let rec has_common_element list1 list2 vars = 
    match list1 with
    | [] -> false, vars 
    | head :: tail ->
      if List.mem head list2 then
        true, head :: vars 
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
    let dep, vars = has_data_dep x y in 
    if dep then p := add_edge !p x y (DataDep vars)
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
  let pdg = ref (traverse_ast block pdg) in
  (* add data dependency edges for each pairs of nodes *)
  apply_pairs (fun x -> fun y -> 
    let dep, vars = has_data_dep x y in 
    if dep then pdg := add_edge !pdg x y (DataDep vars)
  ) !pdg.nodes;
  (* connect the entry node to the header nodes *)
  pdg := begin match !pdg.entry_node with 
  | Some en -> List.fold_left (fun pdg -> fun s -> let n = find_node s pdg in add_edge pdg en n ControlDep) !pdg block
  | None -> !pdg
  end;
  !pdg



(* Strongly connected components using BFS *)


(* let bfs pdg start =
  let n = List.length pdg.nodes in
  let visited = Array.make n false in
  let queue = Queue.create () in
  Queue.add start queue;
  visited.(start) <- true;
  let rec traverse acc =
    if Queue.is_empty queue then acc
    else begin
      let u = Queue.pop queue in
      List.iter (fun v ->
        if not visited.(v) then begin
          Queue.add v queue;
          visited.(v) <- true
        end
      ) pdg.(u);
      traverse (u :: acc)
    end
  in
  List.rev (traverse [])

let scc_bfs pdg =
  let n = List.length pdg.nodes in
  let visited = Array.make n false in
  let components = ref [] in
  let rec bfs_from u =
    let component = bfs pdg u in
    components := component :: !components;
    List.iter (fun v -> visited.(v) <- true) component
  in
  for u = 0 to n - 1 do
    if not visited.(u) then bfs_from u
  done;
  !components


let analysis_pdg pdg =
  let components = scc_bfs pdg in
  List.iter (fun component ->
    Printf.printf "[ ";
    List.iter (Printf.printf "%d ") component;
    Printf.printf "]\n"
  ) components *)