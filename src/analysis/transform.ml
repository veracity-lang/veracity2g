open Ast
open Ast_print
open Format
open Range
open Util
open Exe_pdg


let ctr = ref 0 

let incr_uid (ctr: int ref) =
  ctr := !ctr + 1;
  !ctr

let create_label () : string = 
    "Block" ^ string_of_int (incr_uid ctr)

let mk_blocklabel l : blocklabel =
    (l, None)
 

let rec string_of_stmt_aux (s: exe_stmt node) : string =
    begin match s.elt with 
    | ESIf (e, b1, b2) -> sp "ESIf (%s, %s, %s)"
        (AstML.string_of_exp e) b1 b2
    | ESFor (d,e,s,b) -> sp "For (%s, %s, %s, %s)"
                          (AstML.string_of_list AstML.string_of_vdecl_aux d) 
                          (AstML.string_of_option AstML.string_of_exp e)
                          (AstML.string_of_option AstML.string_of_stmt s) b
    | ESWhile (e,b) -> sp "While (%s, %s)" (AstML.string_of_exp e) b
    (* | ESGoto b -> sp "Goto (%s)" (string_of_stmt_aux b) *)
    | ESSBlock (blocklabel, b) -> let (Some (l, _)) = blocklabel in sp "ESSBlock %s: %s" l (string_of_block b)
    | Stmt s -> AstML.string_of_stmt s 
    end

and string_of_block (b:exe_block node) : string =
    AstML.string_of_list string_of_stmt_aux b.elt


let rec block_to_exeB ?(stmt_list = ref []) (block: block node) pdg : exe_block node =
    (* Printf.printf "block-> %s\n" (AstML.string_of_block block); *)
    match block.elt with
    | [] -> no_loc []
    (* | h::tl -> node_up block (stmt_to_exeS h :: (block_to_exeB @@ no_loc tl).elt) *)
    | stmt::tl -> 
        (* Printf.printf "stmt-> %s\n" (AstML.string_of_stmt stmt); *)
        let es = 
        begin match stmt.elt with 
        | If (e, blk1, blk2) ->
            let head_label = create_label() in
            Printf.printf "lbl => %s\n" head_label;
            let l1 = create_label() in 
            let l2 = create_label() in 
            let s1 = ESSBlock(Some (mk_blocklabel @@ l1), block_to_exeB ~stmt_list:(ref []) blk1 pdg) in 
            let s2 = ESSBlock(Some (mk_blocklabel @@ l2), block_to_exeB ~stmt_list:(ref []) blk2 pdg) in
            pdg := add_node (add_node !pdg s2) s1;
            let new_stmt = ESIf (e, l1, l2) in 
            stmt_list := !stmt_list @ [node_up stmt new_stmt];
            let temp_stmt_list = !stmt_list in 
            stmt_list := [];
            let s = ESSBlock (Some (mk_blocklabel head_label), no_loc temp_stmt_list) in 
            pdg := add_node !pdg s;
            no_loc s
        | For (vdecll, exp, sl, bl) ->
            let head_label = create_label() in
            let l = create_label() in 
            let n = ESSBlock(Some (mk_blocklabel @@ l), block_to_exeB ~stmt_list:(ref []) bl pdg) in 
            pdg := add_node !pdg n;
            let new_stmt = ESFor (vdecll, exp, sl, l) in 
            stmt_list := !stmt_list @ [node_up stmt new_stmt];
            let temp_stmt_list = !stmt_list in 
            stmt_list := [];
            let s = ESSBlock (Some(mk_blocklabel head_label), no_loc temp_stmt_list) in 
            pdg := add_node !pdg s; 
            no_loc s
        | While (e, bl) ->
            let head_label = create_label() in
            let l = create_label() in 
            let n = ESSBlock(Some (mk_blocklabel @@ l), block_to_exeB ~stmt_list:(ref []) bl pdg) in 
            pdg := add_node !pdg n;
            let new_stmt = ESWhile (e, l) in 
            stmt_list := !stmt_list @ [node_up stmt new_stmt];
            let temp_stmt_list = !stmt_list in 
            stmt_list := [];
            let s = ESSBlock (Some(mk_blocklabel head_label), no_loc temp_stmt_list) in 
            pdg := add_node !pdg s; 
            no_loc s 
        | SBlock (blocklabel, bl) -> 
            let s = ESSBlock (blocklabel, block_to_exeB bl pdg) in 
            pdg := add_node !pdg s;
            no_loc s
        | _ -> 
            (* Printf.printf "size ==> %d\n" (List.length !stmt_list); *)
            let s = no_loc @@ Stmt stmt in 
            stmt_list := !stmt_list @ [s] ;
            s
        end 
        in 
        (* Printf.printf "===> %s\n" (string_of_stmt_aux es);  *)
        node_up block (es :: (block_to_exeB ~stmt_list:stmt_list (no_loc tl) pdg).elt)
