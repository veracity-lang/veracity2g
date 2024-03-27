open Ast 


type exe_stmt =
| ESIf of exp node * string * string 
| ESFor of vdecl list * exp node option * stmt node option * string
| ESWhile of exp node * string
| ESSBlock of blocklabel option * exe_block node
| Stmt of Ast.stmt node
 
and exe_block = exe_stmt node list


type dependency =
| ProgramOrder
| Commute of bool
| Disjoint


type edge = {
  src : exe_stmt;
  dst : exe_stmt;
  dep : dependency;
}

type exe_pdg = {
    nodes : exe_stmt list;
    edges : edge list;
}

let empty_exe_pdg () : exe_pdg =
  { nodes = []; edges = [] }

let add_node (pdg : exe_pdg) (n : exe_stmt) : exe_pdg =
  { pdg with nodes = [n] @ pdg.nodes }


let rec apply_pairs f lst =
  match lst with
  | [] -> ()
  | x::xs -> List.iter (fun y -> f x y) xs; apply_pairs f xs

let find_node bl pdg : exe_stmt =
    let (id,_) = bl in 
    List.find (
        fun n -> match n with | ESSBlock (Some(b,None),bl) -> Printf.printf "--> %s\n" b; String.equal b id | _ -> false
    ) pdg.nodes

let add_edge (pdg : exe_pdg) (src : exe_stmt) (dst : exe_stmt) dep : exe_pdg = 
  { pdg with edges = pdg.edges @ [{ src; dst; dep }] }

let rec add_edges (gc_list)  pdg = 
    match gc_list with 
    | [] -> pdg 
    | h::tl ->
        let ((bls,_),c) = h in 
        let dep = Commute c in
        let updated_pdg = ref pdg in 
        apply_pairs (fun [x] -> fun [y] -> 
            let src = find_node x !updated_pdg in 
            let dst = find_node y !updated_pdg in 
            Printf.printf "edge: %s , %s -> %b\n" (fst x) (fst y) c;
            updated_pdg := add_edge !updated_pdg src dst dep;
        ) bls;
        add_edges tl !updated_pdg
    (* !edges *)