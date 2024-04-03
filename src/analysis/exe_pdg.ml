open Ast 
open Ast_print

type dependency =
(* | ProgramOrder *)
| ControlDep
| DataDep
| Commute of bool
| Disjoint


(* type enode = stmt node  *)
(* type enode = Range.t  *)
(* type enode = {
  l : string;
  n : stmt node;
} *)
type enode = {
  l: Range.t; 
  n: stmt 
}

type edge = {
  src : enode;
  dst : enode;
  dep : dependency;
}

type exe_pdg = {
    nodes : enode list;
    edges : edge list;
}

let empty_exe_pdg () : exe_pdg =
  { nodes = []; edges = [] }

let add_node (pdg : exe_pdg) (s : stmt node) : enode * exe_pdg =
  let n = {l = s.loc; n = s.elt} in 
  n, { pdg with nodes = pdg.nodes @ [n] }

  let print_dep = function
  | ControlDep -> "ControlDep"
  | DataDep -> "DataDep"
  | Commute b -> "Commute " ^ (Bool.to_string b)
  | Disjoint -> "Disjoint"

let string_of_pdg_node_stmt s =
  let big_string = Ast_to_c.c_of_stmt s in 
  if String.length big_string > 20 then String.sub big_string 0 19 else big_string


let print_pdg pdg fn : unit = 
  let oc = open_out fn in
  output_string oc (String.concat "\n" [
    "digraph G {\n";
    (* Styles *)
    "  graph [rankdir=\"TB\", fontsize=20, label=\"Black=CFG, Red=ControlDep, Blue=DataDep\", labelloc=t]";
    "  node [shape=box, style=\"rounded,filled\", fontname=\"Courier\", margin=0.05]";
    "  edge [arrowhead=vee, arrowsize=1, fontname=\"Courier\"]";
    (* Nodes *)
    List.fold_left (fun acc node -> acc ^ "\"" ^ (Range.string_of_range_nofn node.l)
    ^ "\" [label=\""^(string_of_pdg_node_stmt node.n)^"\"];\n") "" pdg.nodes;
    (* Edges *)
    List.fold_left (fun acc e -> acc ^ (match e.dep with
       | DataDep -> ""
       | Commute _  
       | Disjoint 
       | ControlDep ->
          "\"" ^ (Range.string_of_range_nofn e.src.l) ^ "\" -> \"" 
               ^ (Range.string_of_range_nofn e.dst.l) ^ "\" "
               ^ "[style=dashed];\n" (*label=\""^(print_dep e.dep)^"\"];\n"*)
    )) "" pdg.edges;
    "}\n";
  ]);
  print_endline ("Graph written to " ^ fn);
  close_out oc


let rec apply_pairs f lst =
  match lst with
  | [] -> ()
  | x::xs -> List.iter (fun y -> f x y) xs; apply_pairs f xs

let find_node (s: stmt node) pdg : enode =
    let sl = s.loc in 
    List.find (
        fun {l=loc;n} -> String.equal (Range.string_of_range loc) (Range.string_of_range sl) 
    ) pdg.nodes

let add_edge (pdg : exe_pdg) (src : enode) (dst : enode) dep : exe_pdg = 
  { pdg with edges = pdg.edges @ [{ src; dst; dep }] }




let rec find_block_vars block = 
  match block with 
  | [] -> []
  | stmt::tl -> (find_stmt_vars stmt) @ (find_block_vars tl)

and find_stmt_vars stmt = 
  match stmt.elt with
  | Assn (e1,e2) -> (find_exp_vars e1) @ (find_exp_vars e2) 
  | Decl vdecl ->
    let id, (_, e) = vdecl in
    id :: find_exp_vars e
  | If (e, b1, b2) -> (find_exp_vars e) @ (find_block_vars b1.elt) @ (find_block_vars b2.elt)
  | While (e, b) -> (find_exp_vars e) @ (find_block_vars b.elt) 
  | _ -> []
  (* | Ret of exp node option
  | SCallRaw of id * exp node list
  | SCall of method_variant * exp node list
  | For of vdecl list * exp node option * stmt node option * block node
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
  | _ -> []
  (* 
  | NewHashTable of hashtable_variant * ty * ty
  | CallRaw of id * exp node list
  | Call of method_variant * exp node list
  | Ternary of exp node * exp node * exp node
  | CStruct of id * exp node bindlist
  | Proj of exp node * id *)

let rec has_data_dep src dst =
  let list1 = find_stmt_vars {elt= src.n; loc= src.l} in 
  let list2 = find_stmt_vars {elt= dst.n; loc= dst.l} in 
  let rec has_common_element list1 list2 = 
    match list1 with
    | [] -> false
    | head :: tail ->
      if List.mem head list2 then
        true 
      else
        has_common_element tail list2 
  in has_common_element list1 list2


let rec apply_pairs f lst =
  match lst with
  | [] -> ()
  | x::xs -> List.iter (fun y -> f x y) xs; apply_pairs f xs

let rec build_pdg (block: block) pdg : exe_pdg =
    match block with
    | [] -> 
      let p = ref pdg in 
      apply_pairs (fun x -> fun y -> 
        if (has_data_dep x y) then p := add_edge !p x y DataDep
      ) pdg.nodes;
      !p
    
    | stmt::tl ->
        let updated_pdg = begin match stmt.elt with 
        | If (e, blk1, blk2) ->
          let src, pdg = add_node pdg stmt in
          let pdg = build_pdg blk2.elt (build_pdg blk1.elt pdg) in 

          let pdg = add_edge pdg src src ControlDep in
          List.fold_left (fun pdg -> fun s -> add_edge pdg src (find_node s pdg) ControlDep) pdg blk1.elt

            
        | While (_, bl) | For (_, _, _, bl) ->
          let src, pdg = add_node pdg stmt in
          let pdg = build_pdg bl.elt pdg in 

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
        build_pdg tl updated_pdg