(* https://www.cs.stevens.edu/~ejk/cs516/20sp/hw/hw04/hw4revised.php *)
open Ast
open Ast_print
open Util
open Vcylib
open Analyze
open Dswp_task
open Option

(*** INTERP MANAGEMENT ***)

let emit_inferred_phis = ref false
let emit_quiet = ref false

let print_cond = ref false

let force_sequential = ref false
let force_infer = ref false

let dswp_mode = ref false

let pool_size = ref 8

let flatten_value_option v = match v with
  | Some v -> v
  | None -> VVoid
  
(* A Job is an unit of work, consisting of:
   - task ID that should perform the job
   - input data for that job is provided in the
     environment as a local, at the topmost call stack frame
  - all non-input will share access (Via references) to the
    shared environment
*)
type job = {
  tid: int;
  env: env;
  (* the environment will have in the stack the input variables:
  vals: (ty * id * value) list 
  exp will only be constants: CInt, CStr, CBool, etc
  *)
}

(*** ENVIRONMENT MANAGEMENT ***)


(* Possible locations of bindings, in order of priority *)
type bind_location =
  | BVLocal of tyval   (* Current function parameter or variable in current block *)
  | BVGlobal of tyval  (* Global variable *)
  | BVUndef                (* Undefined variable *)
  | BMGlobal of tmethod    (* Global method *)
  | BMLib    of lib_method (* Library method *)
  | BMUndef                (* Undefined method *)

type method_data =
  | MGlobal of tmethod
  | MLib of lib_method

let local_env {l;_} =
  match l with
  | b::_ -> List.flatten b
  | _ -> raise @@ UnreachableFailure "Empty callstack"

(* Prioritizes local call stack over global values *)
let current_env env =
  local_env env @ env.g.globals

let push_block_to_callstk env =
  (* debug_print @@ lazy (ColorPrint.color_string Light_red Default "Pushing block.\n"); *)
  let env' = {env with l = ([] :: List.hd env.l) :: List.tl env.l} in
  (* debug_print @@ lazy (ColorPrint.color_string Light_red Default "Block pushed.\n"); *)
  env'

let pop_block_from_callstack {g;l;tid} =
  (* debug_print @@ lazy (ColorPrint.color_string Light_green Default "Popping block.\n"); *)
  { g; l = (List.tl @@ List.hd l) :: List.tl l; tid }

type bind_type =
  | BindM (* Method or function *)
  | BindV (* Global or local variable *)

let find_binding (id : id) (env : env) (t : bind_type) : bind_location =
  match t with
  | BindV ->
    begin match List.assoc_opt id @@ local_env env with
    | Some v -> BVLocal v
    | None ->
      begin match List.assoc_opt id env.g.globals with
      | Some v -> BVGlobal v
      | None -> BVUndef
    end end
  | BindM ->
    begin match List.assoc_opt id env.g.methods with
    | Some m -> BMGlobal m
    | None ->
      begin match List.assoc_opt id env.g.lib_methods with
      | Some lm -> BMLib lm
      | None -> BMUndef
    end end

type thread_result = TRNone | TRErr of exn | TRSome of value

let string_of_thread_result = function
  | TRNone -> "TRNone"
  | TRErr e -> Printf.sprintf "TRErr (%s)" @@ Printexc.to_string e
  | TRSome v -> Printf.sprintf "TRSome (%s)" @@ AstML.string_of_value v

(*let find_value (id : id) (env : env) : value option =
  current_env env |>
  List.assoc_opt id*)

(* TODO does constructing a reference type count as affecting state? What about indexing? *)
(*let rec may_affect_state (env : env) : exp -> bool =
  function
  | Call (id, _) ->
    begin match find_binding id env BindM with
    | BMGlobal _ -> true
    | BMLib (pure,_) -> not pure
    | _ -> false
    end
  | Uop (_,e) -> may_affect_state env e.elt
  | Index (e1,e2) | Bop (_,e1,e2) ->
    may_affect_state env e1.elt || may_affect_state env e2.elt
  | _ -> false*)

let interp_binop_int (op : binop) (loc : Range.t) (v1 : int64) (v2 : int64) : value =
  match op with
  | Eq | Neq | Lt | Lte | Gt | Gte ->
    let f =
      match op with
      | Eq  -> ( = )
      | Neq -> ( <> )
      | Lt  -> ( < )
      | Lte -> ( <= )
      | Gt  -> ( > )
      | Gte -> ( >= )
      | _   -> raise @@ UnreachableFailure "int binop comparison"
    in VBool (f v1 v2)
  | Add | Sub | Mul | IAnd | IOr | Shl | Shr | Sar | Mod | Div | Exp ->
    let f = Int64.(
      match op with
      | Add  -> add
      | Sub  -> sub
      | Mul  -> mul
      | Mod  -> mod64
      | IAnd -> logand
      | IOr  -> logor
      | Shl  -> fun x y -> shift_left x (to_int y)
      | Shr  -> fun x y -> shift_right_logical x (to_int y)
      | Sar  -> fun x y -> shift_right x (to_int y)
      | Div  -> div
      | Exp  -> exp64
      
      | _    -> raise @@ UnreachableFailure "int binop arithmetic"
    )
    in VInt (f v1 v2)
  | _ -> raise @@ TypeFailure ("int binop operator", loc)

let rec interp_unop (env : env) (op : unop) (e : exp node) : env * value =
  let env, v = interp_exp env e in
  match op, v with
  | Lognot, VBool v -> env, VBool (not v)
  | Bitnot, VInt v  -> env, VInt (Int64.lognot v)
  | Neg, VInt v     -> env, VInt (Int64.neg v)
  | _, _            -> raise @@ TypeFailure ("unop argument", e.loc)

(* TODO organize this operation in terms of 'op', rather than in terms of types of values *)
and interp_binop (env : env) (op : binop) (loc : Range.t) (e1 : exp node) (e2 : exp node) : env * value =
  let env, v1 = interp_exp env e1 in
  let env, v2 = interp_exp env e2 in
  match v1, v2 with
  | VNull a', VNull b' when ty_eq env a' b' ->
    begin match op with
    | Eq  -> env, VBool true
    | Neq -> env, VBool false
    | _   -> raise @@ TypeFailure ("binop arguments", loc)
    end
  | VNull a', VNull b' when not @@ ty_eq env a' b' ->
    raise @@ TypeFailure ("Null types are different", loc)
  | a, VNull b' when ty_match env a b' ->
    begin match op with
    | Eq  -> env, VBool false
    | Neq -> env, VBool true
    | _   -> raise @@ TypeFailure ("binop operator with null argument", loc)
    end
  | VNull a', b when ty_match env b a' ->
    begin match op with
    | Eq  -> env, VBool false
    | Neq -> env, VBool true
    | _   -> raise @@ TypeFailure ("binop operator with null argument", loc)
    end

  | VInt v1,  VInt v2  -> env, interp_binop_int op loc v1 v2

  | VBool v1, VBool v2 ->
    let f = 
      match op with
      | Eq  -> ( = )
      | Neq -> ( <> )
      | And -> ( && )
      | Or  -> ( || )
      | _   -> raise @@ TypeFailure ("bool binop operator", loc)
    in env, VBool (f v1 v2)

  | VStr v1, VStr v2   ->
    begin match op with
    | Eq | Neq | Lt | Lte | Gt | Gte ->
      let f =
        match op with
        | Eq  -> ( = )
        | Neq -> ( <> )
        | Lt  -> ( < )
        | Lte -> ( <= )
        | Gt  -> ( > )
        | Gte -> ( >= )
        | _   -> raise @@ UnreachableFailure "string binop comparison"
      in env, VBool (f v1 v2)
    | Concat ->
      env, VStr (v1 ^ v2)
    | _ -> raise @@ TypeFailure ("string binop operator", loc)
    end

  | VStruct (id1, ss1), VStruct (id2, ss2) ->
    if ty_eq env (TStruct id1) (TStruct id2)
    then begin match op with
    | Eq  -> env, VBool (ss1 = ss2)
    | Neq -> env, VBool (ss1 <> ss2)
    | _ -> raise @@ TypeFailure ("struct binop operator", loc)
    end
    else raise @@ TypeFailure ("struct type mismatch", loc)
  | _ -> raise @@ TypeFailure ("binop arguments", loc)

and interp_exp_seq (env : env) : exp node list -> env * value list =
  let rec f (env : env) (values : value list) : exp node list -> env * value list =
    function
    | [] -> env, List.rev values
    | h::t ->
      let env, v = interp_exp env h in
      f env (v :: values) t
  in f env []

and interp_exp_call {g;l;tid} (loc : Range.t) (args : value list) (params : (id * ty) list) (body : block node) : env * value =
  (* Check quantity of arguments *)
  if List.length args <> List.length params
  then raise @@ TypeFailure ("arity mismatch", loc)

  (* Check types of arguments *)
  else if List.exists2 (fun v (_,ty) -> not @@ ty_match {g;l;tid} v ty) args params
  then raise @@ TypeFailure ("argument type mismatch", loc)

  else
    debug_print @@ lazy (ColorPrint.color_string Light_yellow Default "Pushing call.\n");
    (* Associate arguments with IDs *)
    let new_block =
      List.combine
        (List.map fst params)
        (List.combine 
          (List.map snd params) 
          (List.map ref args))
    in let env =
      {g; l = [new_block] :: l; tid}
    in second flatten_value_option (interp_block env body)

and interp_array_of_values (env : env) (loc : Range.t) (ty : ty) (vs : value list) : env * value =
  if List.for_all (fun v -> ty_match env v ty) vs
  then env, VArr (ty, Array.of_list vs)
  else raise @@ TypeFailure ("Types of array values are not all the same", loc)

and interp_exp (env : env) ({elt;loc} : exp node) : env * value =
  match elt with
  | CNull ty -> env, VNull ty
  | CBool v  -> env, VBool v
  | CInt v   -> env, VInt v
  | CStr v   -> env, VStr v
  | CArr (t, ens) -> 
    let env, vs = interp_exp_seq env ens in
    interp_array_of_values env loc t vs
  | NewArr (t, ens) ->
    (* Get length of array *)
    begin match interp_exp env ens with
    | env, VInt i ->
      if i < 0L
      then raise @@ ValueFailure ("array length less than 0", loc)
      else let default_value =
        ty_default_value env t
      (* Make list of constants *)
      in let en =
        List.init (Int64.to_int i) (fun _ -> default_value)
      (* Construct list of constants *)
      in interp_array_of_values env loc t en
    | _, _ -> raise @@ TypeFailure ("new array length is not integer", loc)
    end
  | NewHashTable (variant, tyk, tyv) ->
    let ht =
      let open Hashtables in
      match variant with
      | HTVarSequential -> VHTSequential (Hashtable_seq.make ())
      | HTVarNaiveConcurrent -> VHTNaive (Hashtable_naive.make ())
    in
    env, VHashTable (tyk, tyv, ht)
  | Id id ->
    let values = local_env env @ env.g.globals in
    begin match List.assoc_opt id values with
    | Some (_,v) -> env, !v
    | None -> raise @@ IdNotFound (id, loc)
    end
  | Index (a, i) ->
    begin match interp_exp_seq env [a;i] with
    (* Array index *)
    | env, [VArr (_,a); VInt i] -> env, a.(Int64.to_int i)
    (* Hashtable key application *)
    | env, [VHashTable (tyk, tyv, ht); k] ->
      if not @@ ty_match env k tyk
      then raise @@ TypeFailure ("hashtable key type", loc)
      else 
      let k = htdata_of_value k in
      let res =
        let open Hashtables in
        match ht with
        | VHTNaive t      -> Hashtable_naive.get t k
        | VHTSequential t -> Hashtable_seq.get t k
      in begin match res with
      | None -> env, VNull tyv
      | Some d -> env, value_of_htdata d
      end
    | _, [_;_] -> raise @@ UnreachableFailure "index ID and argument"
    | _        -> raise @@ TypeFailure ("index ID or argument wrong type", loc)
    end
  | Call (mv, args) ->
    let env, args = interp_exp_seq env args in
    begin match mv with
    | MethodM (id, {pure;rty;body;args=params}) ->
      let env, ret = interp_exp_call env loc args params body in
      if ty_match env ret rty
      then env, ret
      else raise @@ TypeMismatchFailure ("Return from function '" ^ id ^ "'", rty, type_of_value ret, loc)
    | MethodL (id, {pure;func;_}) ->
      func (env,args)
    end
  | Bop (op, en1, en2) ->
    interp_binop env op loc en1 en2
  | Uop (op, en)       ->
    interp_unop env op en
  | Ternary (cnd, exp_then, exp_else) ->
    begin match interp_exp env cnd with
    | env, VBool true  -> interp_exp env exp_then
    | env, VBool false -> interp_exp env exp_else
    | _, v             -> raise @@ TypeMismatchFailure ("Ternary condition", TBool, type_of_value v, cnd.loc)
    end
  | CStruct (sname, fields) ->
    (* Check for existence of struct type *)
    let sty =
      match List.assoc_opt sname env.g.structs with
      | Some ty -> ty
      | None -> raise @@ TypeFailure ("Unknown struct " ^ sname, loc)
    (* Check quantity of fields *)
    in let _ =
      if List.length fields <> List.length fields
      then raise @@ TypeFailure ("Field quantity mismatch", loc)
      else ()
    in let ids, es = List.split fields in
    (* Check for unexpected fields *)
    let _ =
      match List.find_opt (fun e_field -> not @@ List.mem_assoc e_field sty) ids with
      | Some id -> raise @@ TypeFailure ("Unexpected field " ^ id, loc)
      | None -> ()
    (* Check for missing fields *)
    in let _ =
      match List.find_opt (fun s_field -> not @@ List.mem s_field ids) (List.map fst sty) with
      | Some id -> raise @@ TypeFailure ("Missing field " ^ id, loc)
      | None -> ()
    (* Evaluate field expressions *)
    in let env, vs = interp_exp_seq env es in
    let ss = List.combine ids @@ List.map ref vs in
    (* Typecheck field values *)
    let _ =
      match List.find_opt 
        (fun (id,v) -> not @@ ty_match env !v (List.assoc id sty)) ss 
      with
      | Some (id,v) -> raise @@ TypeFailure ("Type mismatch for field " ^ id, loc)
      | None -> ()
    in
    env, VStruct (sname, ss)
  | Proj (s, fid) ->
    begin match interp_exp env s with
    | env, VStruct (_, vs) ->
      begin match List.assoc_opt fid vs with
      | Some v -> env, !v
      | None -> raise @@ ValueFailure ("Struct does not have field " ^ fid, loc)
      end
    | _ -> raise @@ TypeFailure ("Projection source is not a struct", loc)
    end
  | CallRaw (id, args) ->
    let env, args = interp_exp_seq env args in
    begin match find_binding id env BindM with
    | BMGlobal {pure;rty;body;args=params} ->
      let env, ret = interp_exp_call env loc args params body in
      if ty_match env ret rty
      then env, ret
      else raise @@ TypeMismatchFailure ("Return from function '" ^ id ^ "'", rty, type_of_value ret, loc)
    | BMLib {pure;func;_} -> 
      func (env,args)
    | BMUndef -> raise @@ IdNotFound (id, loc)
    | _ -> raise @@ UnreachableFailure "call id bind find"
    end

and interp_stmt_assn env loc (lhs : exp node) (rhs : exp node) : env =
  let env, v = interp_exp env rhs in
  match lhs.elt with
  | Id id ->
    begin match find_binding id env BindV with
    | BVUndef -> raise @@ IdNotFound (id, lhs.loc)
    | BVLocal (ty,r)
    | BVGlobal (ty,r) ->
      if ty_match env v ty
      then begin r := v; env end
      else raise @@ TypeFailure ("assignment type mismatch", loc)
    | _ -> raise @@ UnreachableFailure "assn id find bind"
    end
  | Index (a, i) ->
    begin match interp_exp_seq env [a;i] with
    (* Array assignment *)
    | env, [VArr (ty,a); VInt i] -> 
      if not @@ ty_match env v ty
      then raise @@ TypeFailure ("array value type mismatch", loc)
      else
        a.(Int64.to_int i) <- v;
        env
    (* Hashtable assignment *)
    | env, [VHashTable (tyk, tyv, ht); k] ->
      if not @@ ty_match env k tyk
      then raise @@ TypeFailure ("hashtable key type", loc)
      else if not @@ ty_match env v tyv
      then raise @@ TypeFailure ("hashtable value type", loc)
      else begin match v with
      | VNull _ -> raise @@ NotImplemented "Hashtable key removal" (*Hashtbl.remove tbl k;    env*)
      | _       -> 
        let open Hashtables in
        let k = htdata_of_value k in
        let v = htdata_of_value v in
        let _ = (* TODO do something with result? *)
          match ht with
          | VHTNaive h -> Hashtable_naive.put h k v
          | VHTSequential h -> Hashtable_seq.put h k v
        in env
      end
    | _, [_;_] -> raise @@ UnreachableFailure "index ID and argument"
    | _        -> raise @@ TypeFailure ("index ID or argument wrong type", lhs.loc)
    end
  | Proj (s, fid) ->
    begin match interp_exp env s with
    | env, VStruct (id, vs) ->
      begin match List.assoc_opt id env.g.structs with
      | None -> raise @@ UnreachableFailure ("Unknown struct name " ^ id)
      | Some sty ->
        (* Check that field exists *)
        if not @@ List.mem_assoc fid vs
        then raise @@ ValueFailure ("Struct does not have field " ^ fid, lhs.loc)
        (* Check that value of RHS is correct *)
        else if not @@ ty_match env v (List.assoc fid sty)
        then raise @@ TypeFailure ("Type mismatch with RHS and field", loc)
        (* Update struct *)
        else List.assoc fid vs := v;
        env
      end
    | _ -> raise @@ TypeFailure ("Projection source is not a struct", lhs.loc)
    end
  | _ -> raise @@ TypeFailure ("assignment LHS", loc)

and interp_stmt_while (env : env) (loc : Range.t) (cnd : exp node) (body : block node) : env * value option =
  let keep_looping = ref true in
  let ret = ref None in
  let env = ref env in
  while !keep_looping do
    match interp_exp !env cnd with
    | env', VBool false ->
      env := env';
      keep_looping := false
    | env', VBool true ->
      begin match interp_block env' body with
      | env'', Some v ->
        env := env'';
        ret := Some v;
        keep_looping := false
      | env'', None ->
        env := env''
      end
    | _ -> raise @@ TypeFailure ("while condition is not bool", cnd.loc)
  done;
  !env, !ret

and interp_commute_blocks (env : env) : block node list -> env =
  function
  | [] -> env
  | h::t ->
    match interp_block env h with
    | env, None ->
      interp_commute_blocks env t
    | _, Some _ ->
      (* Potentially commutative blocks are not allowed to return anything *)
      raise @@ CommuteFailure ("a block returned something", h.loc)

and interp_commute_async (env : env) (blocks : block node list) : env =
  let results : thread_result array =
    Array.make (List.length blocks) TRNone
  in let make_thread i b =
    let f () =
      results.(i) <-
        try match interp_block env b with
        | _, None   -> TRNone
        | _, Some v -> TRSome v
        with e ->
          TRErr e
    in Parallel.create f

  (* Execute a thread for each block, then join them up *)
  in let threads =
    List.mapi make_thread blocks
  in List.iter Parallel.join threads;

  (* Raise exception if any threads errored or returned a value *)
  results |>
  Array.iteri
    begin fun i r -> 
      begin match r with
      | TRNone -> ()
      | TRSome v ->
        raise @@ CommuteFailure ("Block returned value " ^ AstML.string_of_value v, (List.nth blocks i).loc)
      | TRErr e ->
        raise @@ CommuteFailure ("Block raised exception: " ^ Printexc.to_string e, (List.nth blocks i).loc)
      end
    end;
  env

and interp_psdswp (env:env) (tasklist : dswp_task list) : env =
  failwith "interp_psdswp" 

(* Reject commute condition if it might modify state *)
and interp_phi (env : env) (phi : exp node) : bool =
  (*if may_affect_state env phi.elt
  then raise @@ CommuteFailure ("commutativity condition may affect state", phi.loc)
  else *)
  match interp_exp env phi with
  | _, VBool true  -> true
  | _, VBool false -> false
  | _, _           -> raise @@ TypeFailure ("commutativity condition is not bool", phi.loc)

and interp_return {g;l;tid} (r : value) : env * value option =
  debug_print @@ lazy (ColorPrint.color_string Light_blue Default "Popping call. " ^ AstML.string_of_callstk l ^ "\n");
  { g; l = List.tl l; tid },
  Some r

and interp_global_commute (env: env) : (group_commute node * bool) list =
  let {g; _} = env in
  let rec interp_group_commute g : (group_commute node * bool) list = 
    begin match g with 
    | [] -> []
    | gc::tl -> 
      let _, cc = gc.elt in 
      begin match cc with 
      | PhiExp e ->
        let v = interp_phi env e in
        interp_group_commute tl @ [(gc,v)]
      | PhiInf -> interp_group_commute tl 
      end 
    end
  in 
  (interp_group_commute g.group_commute)
  
and senddep_extend_env env (vals: (ty * id * value) list) : env =
  (* Treat new task as a new block in call stack. *)
  senddep_extend_env_inner {env with l = ([] :: List.hd env.l ) :: List.tl env.l} vals
and senddep_extend_env_inner env vals =
  match vals with 
  | [] -> env 
  | (t,i,v)::rest ->
      (* This is like Decl statements *)
      (* Add ID to environment - most recent call in callstack, innermost block *)
      if List.mem_assoc i env.g.globals then begin
        debug_print (lazy (Printf.sprintf "Dep is global; not creating new reference: %s = %s\n" i (AstML.string_of_value v |> debug_trunc)));
        senddep_extend_env_inner env rest
      end else begin
        debug_print (lazy (Printf.sprintf "Dep sent: %s = %s\n" i (AstML.string_of_value v |> debug_trunc)));
        let stk = List.hd env.l in
        let blk = List.hd stk in
        let blk = (i, (t, ref v)) :: blk in
        let stk = blk :: List.tl stk in
        let env' = {env with l=(stk :: List.tl env.l)} in
        senddep_extend_env_inner env' rest
      end



and interp_stmt (env : env) (stmt : stmt node) : env * value option =
  match stmt.elt with
  | Assn (enl, enr) ->
    interp_stmt_assn env stmt.loc enl enr, None
  | Decl (id, (ty, en)) ->
    let env', v = interp_exp env en in
    if not @@ ty_match env v ty
    then raise @@ TypeFailure ("Assignment type mismatch", stmt.loc)
    else
    (* Add ID to environment - most recent call in callstack, innermost block *)
    let stk = List.hd env'.l in
    let blk = List.hd stk in
    let blk = (id, (ty, ref v)) :: blk in
    let stk = blk :: List.tl stk in
    {env' with l = stk :: List.tl env'.l}, None
  | Ret None ->
    interp_return env VVoid
  | Ret (Some en) ->
    let env, v = interp_exp env en in
    interp_return env v
  | SCallRaw (f, args) ->
    (* Simply a call expression where return value is ignored *)
    let env, _ = interp_exp env @@ node_up stmt @@ CallRaw (f, args) in
    env, None
  | SCall (mv, args) ->
    let env, _ = interp_exp env @@ node_up stmt @@ Call (mv, args) in
    env, None
  | If (cnd, body_then, body_else) ->
    begin match interp_exp env cnd with
    | env, VBool true  -> interp_block env body_then
    | env, VBool false -> interp_block env body_else
    | _, _             -> raise @@ TypeFailure ("if condition is not bool", cnd.loc)
    end
  | For (vdecls, exp_opt, stmt, body) -> 
    let env' = ref (push_block_to_callstk env) in
    (* Iterate over variable declarations *)
    let declare (id,en : vdecl) : unit =
      match interp_stmt !env' @@ {elt=Decl (id,en);loc=Range.norange} with
      | env, None -> env' := env
      | _, _      -> raise @@ UnreachableFailure "declaration statement return"
    in List.iter declare vdecls;
    (* Add loop statement, if it exists, to end of body *)
    let body =
      match stmt with
      | None   -> body
      | Some s -> {elt=body.elt @ [s]; loc=body.loc}
    (* Condition, if not stated, is true *)
    in let cnd =
      match exp_opt with
      | None -> no_loc @@ CBool true
      | Some en -> en
    in
    (* Run for loop as a while loop *)
    let env, v = interp_stmt_while !env' Range.norange cnd body in
    pop_block_from_callstack env, v
  | While (cnd, body) ->
    interp_stmt_while env stmt.loc cnd body
  | Commute (variant, phi, blocks) ->
    let cnd =
      match phi with
      | PhiExp p -> interp_phi env p
      | PhiInf ->
        debug_print @@ lazy (Printf.sprintf 
          "Inferred commute condition at %s is missing; defaulting to 'false'.\n"
          (Range.string_of_range stmt.loc));
        false
    in let commute = cnd && not !force_sequential in
    begin match variant with
    | CommuteVarPar ->
      if commute
      then interp_commute_async env blocks, None
      else interp_commute_blocks env blocks, None
    | CommuteVarSeq ->
      if commute
      then interp_commute_blocks env (shuffle blocks), None
      else interp_commute_blocks env blocks, None
    end
  | Raise e ->
    let env, v = interp_exp env e in
    begin match v with
    | VStr message ->
      raise @@ RuntimeFailure ("Runtime failure: " ^ message, e.loc)
    | _ -> raise @@ TypeFailure ("'raise' argument is not string", e.loc)
    end
  | Assert e ->
    let env, v = interp_exp env e in
    begin match v with
    | VBool true -> env, None
    | VBool false -> raise @@ AssertFailure stmt.loc
    | _ -> raise @@ TypeFailure ("'assert' argument is not bool", e.loc)
    end
  | Assume _ | Havoc _ ->
    env, None (* We simply ignore 'assume's and 'havoc's at runtime *)
  | SBlock (bl, b) ->
    interp_block env b
  | SendDep(task_id, var_id_list) -> 
    (* Tell the scheduler to do it *)
    let job_vals = make_job_vals env var_id_list in
    send_dep (get env.tid) task_id env job_vals;
    
    (* now just return the unmodified environment *)
    env, None
  | SendEOP(task_id) -> 
    Mutex.protect eop_mutex (fun () -> eop_tasks := task_id :: !eop_tasks);
    env, None
  | GCommute(_) -> failwith "gcommute in interp_stmt."
  | Require(_) -> failwith "require in interp_stmt."
(*  | _ -> failwith "interp_stmt: Not Implemented." *)

       (* | SBlock (bl, b) ->
    begin match bl with 
    | None -> interp_block env b 
    | Some l -> interp_block env b
    end; 

    let cnd =
      match phi with
      | PhiExp p -> interp_phi env p
      | PhiInf ->
        debug_print @@ lazy (Printf.sprintf 
          "Inferred commute condition at %s is missing; defaulting to 'false'.\n"
          (Range.string_of_range stmt.loc));
        false
    in let commute = cnd && not !force_sequential in
    if commute
      then interp_commute_async env blocks, None
      else interp_commute_blocks env blocks, None *)

  (* | GCommute (variant, phi, pre, blocks, post) ->
    let cnd =
      match phi with
      | PhiExp p -> interp_phi env p
      | PhiInf ->
        debug_print @@ lazy (Printf.sprintf 
          "Inferred commute condition at %s is missing; defaulting to 'false'.\n"
          (Range.string_of_range stmt.loc));
        false
    in let commute = cnd && not !force_sequential in
    begin match variant with
    | CommuteVarPar ->
      if commute
      then interp_commute_async env blocks, None
      else interp_commute_blocks env blocks, None
    | CommuteVarSeq ->
      if commute
      then interp_commute_blocks env (shuffle blocks), None
      else interp_commute_blocks env blocks, None
    end *)
  
(* and interp_exe_stmt (env: env) (stmt : Exe_pdg.exe_stmt node) : env * value option =
  match stmt.elt with 
  | Stmt s -> interp_stmt env s 
  | _ -> failwith "not implemented" *)

and interp_block ?(new_scope = true) (env : env) (block : block node) : env * value option =
  let stmts = ref block.elt in
  let env = ref (push_block_to_callstk env) in
  let ret = ref None in
  (* Iterate through statements *)
  while !ret = None && !stmts <> [] do
    let e, r = interp_stmt !env @@ List.hd !stmts in
    env   := e; 
    ret   := r;
    stmts := List.tl !stmts
  done;
  (* Pop level from pop stack *)
  let env = !env in
  let ret = !ret in
  let env =
    if ret = None && new_scope
    (* If block returned nothing, pop a block level *)
    then pop_block_from_callstack env
    (* If a return occurred, don't pop anything *)
    else env
  in 
  env, ret

(* let schedule_task tsk () *)


(* PS-DSWP Execution Mode *)

(* A queue of all things that must be joined before we exit. *)
and jobs_mutex = Mutex.create ()
and job_queue = Queue.create ()
and all_jobs = ref []
and run_job jb initial_waits deps = 
    wait_deps jb initial_waits deps (load_task_def jb.tid).body;
    interp_block {jb.env with tid = Some jb.tid} (load_task_def jb.tid).body
(* capture the values of dependent variables from the environment *)
and make_job_vals env deps = 
  List.fold_left (fun acc (varty,varid) ->
      let values = local_env env @ env.g.globals in
      begin match List.assoc_opt varid values with
      | Some (_,v) -> (varty,varid,!v) :: acc
      | None -> raise @@ IdNotFound (varid, Range.norange)
      end          
   ) [] deps
(* Interpreter calls this function at each SendDep to create a new job *)
and add_job j promise =
  Mutex.protect jobs_mutex (fun () ->
    debug_print (lazy (sp "Adding job with tid=%d.\n" j.tid));
    Queue.add (j, promise) job_queue;
    all_jobs := (j, promise) :: !all_jobs)
and new_job ?(wait_on_init = false) j deps = 
  debug_print (Lazy.from_val (sp "Starting new job with tid=%d.\n" j.tid));
  let deps' = topsort_deps deps in
  let initial_waits = if List.is_empty deps' then []
    else begin
      let jobs = Mutex.protect jobs_mutex (fun () -> Queue.to_seq job_queue |> List.of_seq) in
      List.map (fun dep -> List.filter_map (function | ({tid;_}, _) as j -> if tid = dep.pred_task then Some (j, dep) else None) jobs) (List.hd deps' |> List.sort_uniq (fun a b -> b.pred_task - a.pred_task)) |> List.concat
    end in
  let deps'' = if List.is_empty deps' then [] else List.concat (List.tl deps') in
  let promise = Domainslib.Task.async (get !pool) (fun () -> 
    if wait_on_init then Mutex.protect init_mutex (const ());
    run_job j initial_waits deps'' |> seq @@ debug_print (lazy (Printf.sprintf "Job with tid=%d successfully finished.\n" j.tid))) in
  add_job j promise;
  debug_print (Lazy.from_val (sp "Job with tid=%d successfully started.\n" j.tid));

and task_defs = ref []
and pool : Domainslib.Task.pool option ref = ref None
and set_task_def tlist = task_defs := tlist
and load_task_def (taskid:int) : dswp_task = 
  try List.find (fun t -> t.id == taskid) !task_defs
  with Not_found -> failwith "could not find task id"

and join_all () = 
  let ret_value = ref None in
  while not (Queue.is_empty job_queue) do
    begin match Domainslib.Task.await (get !pool) (Mutex.protect jobs_mutex (fun () -> Queue.take job_queue) |> snd) |> snd with
      | Some v -> if is_none !ret_value then ret_value := (Some v)
      | _ -> () end
  done;
  !ret_value

and init_job task_id (env : env) = 
  let env = {env with tid = Some task_id} in

  (* debug_print (lazy (Printf.sprintf "Initializing job with tid=%d\n" task_id)); *)

  let task = load_task_def task_id in
  
  (* Wait for all the dependencies of task *)
  (* This must be done outside of new_job as we grab the resulting state immediately. *)
  (* wait_deps {tid = task_id; env} task.deps_in task.body;
  
  debug_print (lazy (Printf.sprintf "Task %d done waiting.\n" task_id)); *)
  
  (* Now get all the data dependencies *)
  
  (*
  let env' = List.fold_left (
    fun env dep ->
      let jobs = Mutex.protect jobs_mutex (fun () -> Queue.to_seq job_queue) in
      let (j, p) = try Seq.find (fun (j, _) -> j.tid == dep.pred_task) jobs |> Option.get
        with Invalid_argument _ -> failwith (Printf.sprintf "Task id not found: %d" dep.pred_task)
      in
      if not (interp_phi_two dep.commute_cond env j.env task.body (load_task_def j.tid).body)
      (* if it commutes, we don't need to wait *) then begin
    senddep_extend_env env 
      (make_job_vals 
        (try Seq.find (fun (j, _) -> j.tid == dep.pred_task) jobs |> Option.get |> snd |> Domainslib.Task.await (get !pool) |> fst 
        with Invalid_argument _ -> failwith "Unexpected error in init_job.")
       dep.vars) end
       else env
    ) env task.deps_in in
  *)
  (* above isn't necessary since globals are references? TODO: verify this *)
  let env' = env in
  
  (* Now start the job *)
  new_job {tid = task_id; env = env'} task.deps_in ~wait_on_init:true;
  
  (* Mark self as EOP *)
  (*
  Mutex.protect eop_mutex (fun () ->
    debug_print (lazy (Printf.sprintf "EOP: %d\n" task_id));
    eop_tasks := task_id :: !eop_tasks);
  *)
  
and init_mutex = Mutex.create ()
and scheduler init_task env : value option =
  let env', _ = interp_block ~new_scope:false env init_task.decls in
  
  (* Start initial tasks. *)
  Domainslib.Task.run (get !pool) (fun () ->
    Mutex.lock init_mutex;
    List.iter (flip init_job env') init_task.jobs;
    Mutex.unlock init_mutex;
    join_all ())

(* List of things that have sendEOP'd *)
and eop_tasks : int list ref = ref []
and eop_mutex = Mutex.create()
(*
and topsort_tasks_order = ref None
and make_topsort_tasks () =
  (* Just use Kahn's algorithm *)
  let res = ref [] in
  (* We filter based on the spawning graph -- namely all the edges with make_new_job = true *)
  let top = List.filter (fun t -> not (List.exists (fun d -> d.make_new_job) t.deps_in)) !task_defs |> ref in
  while not (List.is_empty !top) do
    let (n :: top') = !top in
    top := top';
    res := n.id :: !res; (* this builds res in reverse topological order *)
    (* I don't want to duplicate or modify the whole pdg structure, so just use a seen list
       (in practice -- res is such a list) and filter with respect to that.
       As implemented, this step has poor performance for large graphs or graphs with many many edges.
       But it's definitely not a bottleneck in the program. *)
       
    (* for each new_task dep out, check that all its deps_in that are make_new_job are in res
       In practice since new_task is 1-1, this shouldn't be necessary and should never evaluate to be true,
       but implementing it like this to play it safe. *)
    List.iter (fun {pred_task; make_new_job;_} -> 
      if make_new_job then begin
        let t : dswp_task = load_task_def pred_task in
        if List.for_all (fun t' -> List.mem t'.pred_task !res) (List.filter (fun d -> d.make_new_job) t.deps_in)
        then top := t :: !top; (* this will end up exploring in dfs order. as long as it's in top order it doesn't matter though *)
      end
    ) n.deps_out
  done;
  topsort_tasks_order := Some (List.rev !res |> List.mapi (fun i e -> (e, i)));
  debug_print (lazy (List.fold_left (fun acc (e, i) -> acc ^ Printf.sprintf "(%d, %d), " e i) "Topsort order: " (get !topsort_tasks_order) ^ "\n"));
*)
and topsort_memo = ref []
and topsort_deps deps =
  (* return deps as a list of lists where the first list has no incoming dependencies, 2nd has only from the 1st, etc *)
  (* There may be a smarter way to do this but since we only have <10 tasks, I'm going to brute force + memoize. *)
  
  match List.assoc_opt deps !topsort_memo with
  | Some res -> res
  | None -> begin
      let get_pred_task = function {pred_task; _} -> pred_task in
      let remaining = ref deps in
      let dep_tasks = List.map get_pred_task deps in
      let seen : dependency list ref = ref [] in
      let res = ref [] in
      while List.is_empty !remaining |> not do
        let (level, others) = List.partition (fun dep ->
          (* Get all the dependencies whose pred_task has
             incoming spawning tasks from deps be only from seen tasks *)
          let t = load_task_def dep.pred_task in
          List.filter (fun dep' -> dep'.make_new_job && List.mem dep'.pred_task dep_tasks) t.deps_in |>
          List.for_all (fun dep' -> List.mem dep'.pred_task (List.map get_pred_task !seen))) !remaining in
          res := level :: !res;
          seen := level @ !seen;
          remaining := others;
      done;
      let res' = List.rev !res in
      topsort_memo := (deps, res') :: !topsort_memo;
      res'
  end

and bind_formals formals body env : (string * tyval) list list =
  match formals with
  | [] -> [[]]
  | xs -> begin match body.elt with
    | [{elt=SBlock(Some (_, Some vars), _); _}] ->
     (* List.iter (fun s -> print_string(s ^ "\n")) formals;
     List.iter (fun var -> interp_exp env var |> snd |> AstML.string_of_value |> print_string ) vars; *)
     [List.combine formals (List.map (fun var -> interp_exp env var |> snd |> fun v -> (type_of_value v, ref v)) vars)]
    | stmts -> debug_print (lazy "Expected formals, but did not find singleton, labeled block.\n"); List.iter (compose Lazy.from_val AstML.string_of_stmt |> compose debug_print) stmts; failwith "Expected formals, but did not find singleton, labeled block."
  end
and wait_eop task_id =
  let eop_list = ref [] in
  Mutex.protect eop_mutex (fun () -> eop_list := !eop_tasks);
  while not (List.mem task_id !eop_list) do
      Unix.sleepf 0.01;
      Mutex.protect eop_mutex (fun () -> eop_list := !eop_tasks)
  done
and interp_phi_two {my_task_formals=formals; other_task_formals=formals'; condition = cond; _} lenv renv lbody rbody =
  match cond with
  | Some phi ->
      interp_phi {lenv with l = (bind_formals formals lbody lenv @ bind_formals formals' rbody renv) :: []} phi
  | None -> false
and wait_deps j init_waits deps self_body =
  (* Wait for everything we need to EOP to EOP. *)
  (* As per discussion, forego EOP waiting. *)
  (* List.iter (fun dep -> wait_eop dep.pred_task) deps; *)
  
  (* debug_print (lazy (Printf.sprintf "%d's unsorted deps: " (Option.value j.env.tid ~default:(-1)) ^ List.fold_left (fun acc e -> acc ^ Printf.sprintf "%d " e.pred_task) "" deps ^ "\n")); *)
  
  (* topologically sort the dependencies *)
  (* This should already be done by this point *)
  (*
  let deps' = 
    let order_index = get !topsort_tasks_order in
    List.fast_sort (fun x y -> List.assoc x.pred_task order_index - List.assoc y.pred_task order_index) deps
  in
  *)
  
  (* debug_print (lazy (Printf.sprintf "%d's sorted deps: " (Option.value j.env.tid ~default:(-1)) ^ List.fold_left (fun acc e -> acc ^ Printf.sprintf "%d " e.pred_task) "" deps' ^ "\n")); *)
  let my_id = (Option.value j.env.tid ~default:(-1)) in
  
  debug_print (lazy (Printf.sprintf "%d's deps: (jobs with tid: %s) (tasks: %s)\n"
    my_id 
    (List.fold_left (fun acc e -> acc ^ Printf.sprintf "%d " (fst e |> fst).tid) "" init_waits)
    (List.fold_left (fun acc e -> acc ^ Printf.sprintf "%d " e.pred_task) "" deps)));
  
  let wait_job (j', promise) = function
      | {commute_cond = { condition = None; _ }; _} ->
          debug_print (lazy (Printf.sprintf "%d: Waiting on job dependency %d.\n" my_id j'.tid));
          Domainslib.Task.await (get !pool) promise |> ignore;
          debug_print (lazy (Printf.sprintf "%d: Done waiting on job dependency %d.\n" my_id j'.tid))
      | {commute_cond = cond; _}
        when not (interp_phi_two cond j.env j'.env self_body (load_task_def j'.tid).body) ->
          debug_print (lazy (Printf.sprintf "%d: Commute condition not met. Waiting on job %d.\n" my_id j'.tid));
          Domainslib.Task.await (get !pool) promise |> ignore;
          debug_print (lazy (Printf.sprintf "%d: Done waiting on job dependency %d.\n" my_id j'.tid))
      | _ -> debug_print (lazy (Printf.sprintf "%d: Commute condition with %d met. Skipping.\n" my_id j'.tid))
  in
  
  (* wait on every initial job *)
  List.iter (uncurry wait_job) init_waits;
  
  (* For each dependency in order, wait on all jobs we're dependent on. *)
  List.iter (fun d ->
    let jobs = Mutex.protect jobs_mutex (fun () -> !all_jobs) in
    (* Get the jobs corresponding to this dependency *)
    let jobs_to_wait = List.filter (fun (j', _) -> 
      j'.tid = d.pred_task && if j'.tid = j.tid then j'.tid < j.tid else true) jobs in
    List.iter (flip wait_job d) jobs_to_wait
  ) deps;

and send_dep calling_tid tid env vals =
  (* 1 - Check input dependencies
       1a - If it doesn't commute, then wait for EOP and for all of them to join.
            (For now we poll, can add ourselves to a list of processes to be woken up when EPO happens)
       1a - If it's a commute condition, still wait for EOP,
            Check all existing jobs and check commutativity condition between them.
     2 - Create new environment, and create new job.
  *)
  
  debug_print (lazy (Printf.sprintf "send_dep called for tid=%d\n" tid));
  
  let env' = senddep_extend_env env vals in
  let env' = {env' with tid = Some tid} in
  
  (* 1 *)
  let task = load_task_def tid in
  let deps =
    List.filter (function
      | {pred_task;_} when pred_task = calling_tid -> false (* Skip calling task *)
      | {commute_cond = {condition = Some phi; _}; _} -> true
      | _ -> true ) task.deps_in
  in
  (* debug_print (lazy (Printf.sprintf "send_dep: %d dependencies\n" (List.length deps))); *)
  
  (* Wait on dependencies to finish executing. *)
  (* wait_deps env' deps task.body; 
    This is now handled during job creation.
  *)
  
  (* 2  -- make the new job *)
  (* TODO: What env? All non-deps are just global, no? Just use outer env. *)
  new_job {tid; 
    env = env'} deps

(* Draft of new scheduler that accumulates dependencies *)
(*
let received_dependencies = ref []
let dep_mutex = Mutex.create()
let env0 = ref None
let scheduler' env =
  env0 := Some env;
  (* Start initial jobs -- one with no input dependencies. *)
  List.filter (fun task -> null task.deps_in) !task_defs
  |> List.map (fun task -> {tid=task.id; env=env})
  |> List.iter new_job;
  Domainslib.Task.run !pool join_all
  
let send_dep tfrom tto vals =
  (* Receive the new dependency *)
  Mutex.lock dep_mutex;
  let pre_deps = !received_dependencies in
  let post_deps = (tfrom, tto, vals) :: pre_deps in
  received_dependencies := post_deps;
  Mutex.unlock dep_mutex;
  
  (* Check if that was the last dependency we needed *)
  let task = load_task_def tto in
  let relevant_deps = List.filter (fun (_, tto', _) -> tto' = tto) post_deps in
  if List.for_all (fun from -> 
    List.exists (fun (from', _, _) -> from' = from) relevant_deps) task.deps_in
    (* TODO: check that all the variables sent are the ones we needed? *)
  then new_job {tid = tto; 
    env = List.fold_left senddep_extend_env (Option.get !env0) (List.map trd relevant_deps)}
*)


(*** COMMUTATIVITY INFERENCE ***)

(* Globals are relative to the blocks *)
let infer_phi (g : global_env) (var : commute_variant) (bl : block node list) (globals : ty bindlist) pre post : exp node =
  let e = Analyze.phi_of_blocks g var bl globals pre post in
  no_loc e

let labeled_blocks = ref []
let global_defs = ref []

let find_blocks_by_label labels = 
  let blks = ref [] in
  List.iter (fun ls -> List.iter (fun (id, args) -> 
    let [@warning "-8"] {elt=SBlock(Some(i,_),bl);_} = List.find 
      (function {elt=SBlock(Some(i,_),a);_} -> String.equal i id | _ -> false) !labeled_blocks 
    in blks := !blks @ [bl]) ls) labels;
  !blks

(* Find the index of the first occurrence of x in list l *)
let rec find_index x l =
  let rec aux x l idx =
    match l with
    | [] -> -1 (* x not found *)
    | h :: t -> if h.elt = x.elt then idx else aux x t (idx + 1)
  in
  aux x l 0

let find_corresponding a b s =
  let idx = find_index s b in
  if idx == -1 then None
  else Some (List.nth a idx)
    

let rec substitute_vars_exp (args_in: exp node list) (args_out: exp node list) exp = 
  let e = match exp.elt with 
  | CStr _ | Id _ -> find_corresponding args_in args_out exp
  | Index (e1, e2) -> Some (node_up exp (Index (substitute_vars_exp args_in args_out e1, substitute_vars_exp args_in args_out e2)))
  | Bop (op, e1, e2) -> Some (node_up exp @@ Bop (op, substitute_vars_exp args_in args_out e1, substitute_vars_exp args_in args_out e2))
  | Uop (op, e) -> Some (node_up exp @@ Uop (op, substitute_vars_exp args_in args_out e))
  | CallRaw (id, el) -> Some (node_up exp @@ CallRaw (id, List.map (substitute_vars_exp args_in args_out) el))
  | Call (method_variant, el) -> Some (node_up exp @@ Call (method_variant, List.map (substitute_vars_exp args_in args_out) el))
  | CNull _ | CBool _ | CInt _ -> None
  | _ -> None
  (* 
  | CArr of ty * exp node list
  | NewArr of ty * exp node
  | NewHashTable of hashtable_variant * ty * ty
  | Ternary of exp node * exp node * exp node
  | CStruct of id * exp node bindlist
  | Proj of exp node * id
    *)
  in 
  match e with
  | None -> exp 
  | Some ex -> ex
    
let rec substitute_vars_block (args_in: exp node list) (args_out: exp node list) block = 
  match block with 
  | [] -> block
  | s::tl -> 
  let s' = begin match s.elt with 
  | Assn (e1,e2) -> Assn (substitute_vars_exp args_in args_out e1, substitute_vars_exp args_in args_out e2)
  | If (e,b1,b2) -> If (substitute_vars_exp args_in args_out e, node_up b1 @@ substitute_vars_block args_in args_out b1.elt, node_up b2 @@ substitute_vars_block args_in args_out b2.elt)
  | Ret (Some e) -> Ret (Some (substitute_vars_exp args_in args_out e))
  | Decl (id, (ty, e)) -> Decl (id,(ty,substitute_vars_exp args_in args_out e))
  | SCallRaw (id, el) -> SCallRaw (id, List.map (substitute_vars_exp args_in args_out) el)
  | SCall (method_variant, el) -> SCall (method_variant, List.map (substitute_vars_exp args_in args_out) el)
  (* 
  
  | For of vdecl list * exp node option * stmt node option * block node
  | While of exp node * block node
  | Raise of exp node
  | Commute of commute_variant * commute_condition * block node list
  | Assert of exp node
  | Assume of exp node
  | Havoc of id
  | Require of exp node
  | SBlock of blocklabel option * block node
  | GCommute of commute_variant * commute_condition * commute_pre_cond * block node list * commute_post_cond
  | SendDep of int * ((ty * id) list) (* only for dependency of tasks *)
  | SendEOP of int *)
  | _ -> s.elt
  end 
  in (node_up s s') :: substitute_vars_block args_in args_out tl
  
let infer_phis_of_global_commutativity (g : global_env) (defs : ty bindlist) : group_commute node list = 
  let rec interp_group_commute (gc: group_commute node list) : group_commute node list = 
    begin match gc with 
    | [] -> [] 
    | gc::tl -> 
      let labels, phi = gc.elt in 
      let blks = ref [] in
      List.iter (
        fun ls -> 
          List.iter (
            fun (id, args) ->
            let {elt=SBlock(Some(i,args'),bl);_} = List.find (fun {elt=SBlock(Some(i,_),a);_} -> String.equal i id) !labeled_blocks in
            let bl' = match args, args' with 
            | Some a, Some a' -> 
            (* List.iter (fun x -> Printf.printf "args: %s \n" (AstML.string_of_exp x)) a;
            List.iter (fun x -> Printf.printf "args': %s \n" (AstML.string_of_exp x)) a'; *)
            let b' = node_up bl (substitute_vars_block a a' bl.elt) in
            (* Printf.printf "==> %s \n" (AstML.string_of_block b'); *)
            b'
            | _, _ -> bl
            in 
            blks := !blks @ [bl']
          ) ls
      ) labels;
      let phi' =
        let infer () =
        (* apply_pairs (fun b1 b2 -> infer_phi g CommuteVarPar (b1@b2) defs None None) !blks  *)
        let phi' = infer_phi g CommuteVarPar !blks defs None None in
          if !emit_inferred_phis then
            begin if !emit_quiet
            then Printf.printf "%s\n"
              (AstPP.string_of_exp phi')
            else Printf.printf "Inferred condition at %s: %s\n"
              (Range.string_of_range gc.loc) 
              (AstPP.string_of_exp phi')
            end;
          phi'
        in match phi with
      | PhiExp e -> if !force_infer then infer () else e
      | PhiInf -> infer ()

      in let c = {gc with elt = (labels, PhiExp phi')} in
      (List.cons c)
      (interp_group_commute tl)
    end
  in 
  interp_group_commute g.group_commute


let rec infer_phis_of_block (g : global_env) (defs : ty bindlist) (body : block node) : block node =
  global_defs := remove_duplicate (defs @ !global_defs);
  if body.elt = [] then node_up body [] else
  let h,t = List.hd body.elt, node_app List.tl body in
  match h.elt with
  | Assn _ | Ret _ | SCall _ | SCallRaw _
  | Raise _ | Assert _ | Assume _  | Havoc _ | Require _ -> 
    node_app
    (List.cons h)
    (infer_phis_of_block g defs t)
  | Decl (id,(ty,e)) ->
    let defs' = (id, ty) :: defs in
    node_app
      (List.cons h)
      (infer_phis_of_block g defs' t)
  | If (e,b1,b2) ->
    let s = If (e, infer_phis_of_block g defs b1, infer_phis_of_block g defs b2) in
    node_app
      (List.cons (node_up h s))
      (infer_phis_of_block g defs t)
  | For (decls,e,s,b) ->
    let defs' = List.fold_left 
      (fun defs (id,(ty,e)) -> 
        (id, ty) :: defs) 
      defs decls
    in let s = For (decls,e,s,infer_phis_of_block g defs' b)
    in node_app
      (List.cons (node_up h s))
      (infer_phis_of_block g defs t)
  | While (e,b) ->
    let s = While (e, infer_phis_of_block g defs b) in
    node_app
      (List.cons (node_up h s))
      (infer_phis_of_block g defs t)
  | Commute (var,phi,bl) ->
    let bl = List.map (infer_phis_of_block g defs) bl in
    let phi' =
      let infer () = let phi' = infer_phi g var bl defs None None in
        if !emit_inferred_phis then
          begin if !emit_quiet
          then Printf.printf "%s\n"
            (AstPP.string_of_exp phi')
          else Printf.printf "Inferred condition at %s: %s\n"
            (Range.string_of_range h.loc) 
            (AstPP.string_of_exp phi')
          end;
        phi'
      in match phi with
    | PhiExp e -> if !force_infer then infer () else e
    | PhiInf -> infer ()
    in let s = Commute (var, PhiExp phi', bl) in
    node_app
      (List.cons (node_up h s))
      (infer_phis_of_block g defs t)
  | SBlock (bl, b) ->
    let s = SBlock (bl, infer_phis_of_block g defs b) in
    begin match bl with
    | Some _ -> labeled_blocks := !labeled_blocks @ [node_up h s]
    | None -> ()
    end;
    node_app
      (List.cons (node_up h s))
      (infer_phis_of_block g defs t)
  | GCommute (var,phi,pre,bl,post) ->
  let bl = List.map (infer_phis_of_block g defs) bl in
  let phi' =
    let infer () = let phi' = infer_phi g var bl defs (Some pre) (Some post) in
      if !emit_inferred_phis then
        begin if !emit_quiet
        then Printf.printf "%s\n"
          (AstPP.string_of_exp phi')
        else Printf.printf "Inferred condition at %s: %s\n"
          (Range.string_of_range h.loc) 
          (AstPP.string_of_exp phi')
        end;
      phi'
    in match phi with
    | PhiExp e -> if !force_infer then infer () else e
    | PhiInf -> infer ()
    in let s = Commute (var, PhiExp phi', bl) in
    node_app
      (List.cons (node_up h s))
      (infer_phis_of_block g defs t)
  | SendDep (_, _) | SendEOP(_) -> failwith "sendDep/sendEOP should not be in infer_phis_of_block."

let infer_phis_of_prog (g : global_env) : global_env =
  let globals : ty bindlist =
    List.map (fun (i,(ty,_)) -> i,ty) g.globals 
  in let map_method (i,m : tmethod binding) =
    i,
    { m with
      body = infer_phis_of_block g (m.args @ globals) m.body
    }
  in
  let m = List.map map_method g.methods in
  let gc = infer_phis_of_global_commutativity g !global_defs in
  { g with methods = m; group_commute = gc }

let verify_phis_of_global_commutativity (g : global_env) (defs : ty bindlist) : unit = 
  let rec interp_group_commute (gc: group_commute node list) : unit = 
    begin match gc with 
    | [] -> () 
    | gc::tl -> 
      let labels, phi = gc.elt in 
      let blks = ref [] in
      List.iter (
        fun ls -> 
          List.iter (
            fun (id, args) ->
            let {elt=SBlock(Some(i,args'),bl);_} = List.find (fun {elt=SBlock(Some(i,_),a);_} -> String.equal i id) !labeled_blocks in
            let bl' = match args, args' with 
            | Some a, Some a' -> 
            node_up bl (substitute_vars_block a a' bl.elt)
            | _, _ -> bl
            in 
            blks := !blks @ [bl']
          ) ls
      ) labels;
      begin match phi with
      | PhiExp e ->
        if !print_cond then 
          Printf.printf "%s\n" (AstPP.string_of_exp e);

        begin match Analyze.verify_of_block e g CommuteVarPar !blks defs None None with
        | Some b, compl -> 
          let compl_str = 
            match compl with 
            | Some true  -> "true" 
            | Some false -> "false" 
            | None       -> "unknown"
          in
          if not b then begin 
            if not !emit_quiet then Printf.printf "Condition at %s verified as incorrect: %s\n" 
              (Range.string_of_range gc.loc) 
              (AstPP.string_of_exp e)
            else print_string "incorrect\n"
          end else begin 
            if not !emit_quiet then
              Printf.printf "Condition at %s verified as correct: %s\nComplete status: %s\n"
                (Range.string_of_range gc.loc) 
                (AstPP.string_of_exp e)
                compl_str
            else Printf.printf "correct\n%s\n" compl_str
          end
        | None, _ -> 
          if not !emit_quiet then
            Printf.printf "Condition at %s unable to verify: %s\n" 
              (Range.string_of_range gc.loc) 
              (AstPP.string_of_exp e)
          else print_string "failure\n"
        end
      | PhiInf -> () end;
      (interp_group_commute tl)
    end
  in 
  interp_group_commute g.group_commute


let rec verify_phis_of_block (g : global_env) (defs : ty bindlist) (body : block node) : block node =
  global_defs := remove_duplicate (defs @ !global_defs);
  if body.elt = [] then node_up body [] else
  let h,t = List.hd body.elt, node_app List.tl body in
  match h.elt with
  | Assn _ | Ret _ | SCall _ | SCallRaw _
  | Raise _ | Assert _ | Assume _  | Havoc _ -> 
    node_app
    (List.cons h)
    (verify_phis_of_block g defs t)
  | Decl (id,(ty,e)) ->
    let defs' = (id, ty) :: defs in
    node_app
      (List.cons h)
      (verify_phis_of_block g defs' t)
  | If (e,b1,b2) ->
    let s = If (e, verify_phis_of_block g defs b1, verify_phis_of_block g defs b2) in
    node_app
      (List.cons (node_up h s))
      (verify_phis_of_block g defs t)
  | For (decls,e,s,b) ->
    let defs' = List.fold_left 
      (fun defs (id,(ty,e)) -> 
        (id, ty) :: defs) 
      defs decls
    in let s = For (decls,e,s,verify_phis_of_block g defs' b)
    in node_app
      (List.cons (node_up h s))
      (verify_phis_of_block g defs t)
  | While (e,b) ->
    let s = While (e, verify_phis_of_block g defs b) in
    node_app
      (List.cons (node_up h s))
      (verify_phis_of_block g defs t)
  | SBlock (bl, b) ->
    let s = SBlock (bl, verify_phis_of_block g defs b) in
    begin match bl with
    | Some _ -> labeled_blocks := !labeled_blocks @ [node_up h s]
    | None -> ()
    end;
    node_app
      (List.cons (node_up h s))
      (verify_phis_of_block g defs t)
  | Commute (var,phi,bl) ->
    let bl = List.map (verify_phis_of_block g defs) bl in
    begin match phi with
      | PhiExp e ->
        if !print_cond then 
          Printf.printf "%s\n" (AstPP.string_of_exp e);

        begin match Analyze.verify_of_block e g var bl defs None None with
        | Some b, compl -> 
          let compl_str = 
            match compl with 
            | Some true  -> "true" 
            | Some false -> "false" 
            | None       -> "unknown"
          in
          if not b then begin 
            if not !emit_quiet then Printf.printf "Condition at %s verified as incorrect: %s\n" 
              (Range.string_of_range h.loc) 
              (AstPP.string_of_exp e)
            else print_string "incorrect\n"
          end else begin 
            if not !emit_quiet then
              Printf.printf "Condition at %s verified as correct: %s\nComplete status: %s\n"
                (Range.string_of_range h.loc) 
                (AstPP.string_of_exp e)
                compl_str
            else Printf.printf "correct\n%s\n" compl_str
          end
        | None, _ -> 
          if not !emit_quiet then
            Printf.printf "Condition at %s unable to verify: %s\n" 
              (Range.string_of_range h.loc) 
              (AstPP.string_of_exp e)
          else print_string "failure\n"
        end
      | PhiInf -> () end;
    let s = Commute (var, phi, bl) in
    node_app
      (List.cons (node_up h s))
      (verify_phis_of_block g defs t)
  | GCommute (var,phi,pre,bl,post) ->
    let bl = List.map (verify_phis_of_block g defs) bl in
    begin match phi with
      | PhiExp e ->
        if !print_cond then 
          Printf.printf "%s\n" (AstPP.string_of_exp e);

        begin match Analyze.verify_of_block e g var bl defs (Some pre) (Some post) with
        | Some b, compl -> 
          let compl_str = 
            match compl with 
            | Some true  -> "true" 
            | Some false -> "false" 
            | None       -> "unknown"
          in
          if not b then begin 
            if not !emit_quiet then Printf.printf "Condition at %s verified as incorrect: %s\n" 
              (Range.string_of_range h.loc) 
              (AstPP.string_of_exp e)
            else print_string "incorrect\n"
          end else begin 
            if not !emit_quiet then
              Printf.printf "Condition at %s verified as correct: %s\nComplete status: %s\n"
                (Range.string_of_range h.loc) 
                (AstPP.string_of_exp e)
                compl_str
            else Printf.printf "correct\n%s\n" compl_str
          end
        | None, _ -> 
          if not !emit_quiet then
            Printf.printf "Condition at %s unable to verify: %s\n" 
              (Range.string_of_range h.loc) 
              (AstPP.string_of_exp e)
          else print_string "failure\n"
        end
      | PhiInf -> () end;
    let s = Commute (var, phi, bl) in
    node_app
      (List.cons (node_up h s))
      (verify_phis_of_block g defs t)
  | SendDep (_, _) | SendEOP(_) | Require(_) -> failwith "sendDep/sendEOP/require should not be present in verify_phis."

let verify_phis_of_prog (g : global_env) : global_env =
  let globals : ty bindlist =
    List.map (fun (i,(ty,_)) -> i,ty) g.globals 
  in let map_method (i,m : tmethod binding) =
    i,
    { m with
      body = verify_phis_of_block g (m.args @ globals) m.body
    }
  in
  let m = List.map map_method g.methods in
  verify_phis_of_global_commutativity g !global_defs;
  { g with methods = m }
(* TODO: The above is mostly copy pasted from infer. Could just be a _ -> () pass of the AST instead of typed as a transformation. *)

(*** ENVIRONMENT CONSTRUCTION ***)

type texp_list = (ty * exp node) bindlist

(* Build up environment of methods, functions, lib_methods, and structs
 * Global declarations aren't evaluated yet *)
let rec construct_env (g : global_env) (globals : texp_list) : prog -> global_env * texp_list =
  function
  | [] -> { g with lib_methods = lib_methods }, globals
  | Gvdecl {elt = {name; ty; init}; loc = _} :: tl ->
    construct_env g ((name,(ty,init)) :: globals) tl
  | Gmdecl {elt = {pure;mrtyp;mname;args;body}; loc = l} :: tl ->
    (* let gc_list = interp_global_commute g in  *)
    (* Exe_pdg.ps_dswp body l args g globals; *)

    (* Eric's testing of Vcy-to-C. This will later be called with the re-constructed task bodies *)
    (* Codegen_c.gen body.elt; *)
    (* Codegen_c.gen_tasks (Task.example_var_decls ()) (Task.example_tasks ()); *)
    (* Codegen_c.print_tasks (Task.example_tasks ()) "/tmp/tasks.dot"; *)

    let m =
      { pure
      ; rty = mrtyp
      ; args = List.map swap args
      ; body
      }
    in construct_env {g with methods = (mname,m) :: g.methods } globals tl
  | Gsdecl {elt = {sname;fields}; loc = _} :: tl ->
    let s = sname, List.map (fun {field_name;ftyp} -> field_name,ftyp) fields
    in construct_env {g with structs = s :: g.structs} globals tl
  | Commutativity gc :: tl ->
    construct_env {g with group_commute = gc} globals tl

(* Convert all SCallRaw to SCall, and CallRaw to Call 
 * All that needs adjusting is methods.
 * Globals have already been evaluated.
 *)
let cook_calls (g : global_env) : global_env =
  let rec cook_calls_of_exp (e : exp node) : exp node =
    let e' =
      match e.elt with
      | CArr (t, el) ->
        CArr (t, List.map cook_calls_of_exp el)
      | NewArr (t, e) ->
        NewArr (t, cook_calls_of_exp e)
      | Index (e1, e2) ->
        Index (cook_calls_of_exp e1, cook_calls_of_exp e2)
      | CallRaw (id, el) ->
        let el = List.map cook_calls_of_exp el in
        begin match find_binding id {g;l=[];tid=None} BindM with
        | BMGlobal mv ->
          Call (MethodM (id, mv), el)
        | BMLib mv -> 
          Call (MethodL (id, mv), el)
        | BMUndef -> raise @@ IdNotFound (id, e.loc)
        | _ -> raise @@ UnreachableFailure "bind find"
        end
      | Call _ -> raise @@ UnreachableFailure "cook_calls_of_exp Call"
      | Bop (b, e1, e2) ->
        Bop (b, cook_calls_of_exp e1, cook_calls_of_exp e2)
      | Uop (u, e) ->
        Uop (u, cook_calls_of_exp e)
      | Ternary (e1, e2, e3) ->
        Ternary (cook_calls_of_exp e1, cook_calls_of_exp e2, cook_calls_of_exp e3)
      | CStruct (id, el) ->
        CStruct (id, List.map (fun (i, e) -> i, cook_calls_of_exp e) el)
      | Proj (e, i) ->
        Proj (cook_calls_of_exp e, i)
      | Id _ | CNull _ | CBool _ 
      | CInt _ | CStr _ | NewHashTable _ -> e.elt
    in
    node_up e e'
  in

  let cook_calls_of_vdecl (i, (t, e) : vdecl) : vdecl =
    i, (t, cook_calls_of_exp e)
  in
  
  let rec cook_calls_of_stmt (s : stmt node) : stmt node =
    let s' = match s.elt with
    | Assn (e1, e2) ->
      Assn (cook_calls_of_exp e1, cook_calls_of_exp e2)
    | Decl v ->
      Decl (cook_calls_of_vdecl v)
    | Ret e ->
      Ret (Option.map cook_calls_of_exp e)
    | SCallRaw (id, el) ->
      let el = List.map cook_calls_of_exp el in
      begin match find_binding id {g;l=[];tid=None} BindM with
      | BMGlobal mv ->
        SCall (MethodM (id, mv), el)
      | BMLib mv -> 
        SCall (MethodL (id, mv), el)
      | BMUndef -> raise @@ IdNotFound (id, s.loc)
      | _ -> raise @@ UnreachableFailure "bind find"
      end
    | SCall _ -> raise @@ UnreachableFailure "cook_calls_of_stmt SCall"
    | If (e, b1, b2) ->
      If (cook_calls_of_exp e, cook_calls_of_block b1, cook_calls_of_block b2)
    | For (vl, e, ss, b) ->
      let vl = List.map cook_calls_of_vdecl vl in
      let e = Option.map cook_calls_of_exp e in
      let ss = Option.map cook_calls_of_stmt ss in
      let b = cook_calls_of_block b in
      For (vl, e, ss, b)
    | While (e, b) ->
      While (cook_calls_of_exp e, cook_calls_of_block b)
    | Raise e ->
      Raise (cook_calls_of_exp e)
    | Commute (v, c, bl) ->
      let c =
        match c with
        | PhiExp e -> PhiExp (cook_calls_of_exp e)
        | PhiInf -> PhiInf
      in
      Commute (v, c, List.map cook_calls_of_block bl)
    | Assert e ->
      Assert (cook_calls_of_exp e)
    | Assume e ->
      Assume (cook_calls_of_exp e)
    | Havoc id ->
      Havoc id
    | Require e ->
      Require (cook_calls_of_exp e)
    | SBlock (bl, b) ->
      begin match bl with 
      | None -> SBlock(None, cook_calls_of_block b) 
      | Some l -> 
        SBlock(Some l, cook_calls_of_block b)
      end
    | GCommute (v, c, pre, bl, post) ->
      let c =
        match c with
        | PhiExp e -> PhiExp (cook_calls_of_exp e)
        | PhiInf -> PhiInf
      in
      GCommute (v, c, cook_calls_of_exp pre, List.map cook_calls_of_block bl, cook_calls_of_exp post)
    | SendDep (_, _) | SendEOP(_) -> failwith "sendDep/sendEOP should not be present in cook_calls."
    in
    node_up s s'

  and cook_calls_of_block b =
    node_app (List.map cook_calls_of_stmt) b
  in
  
  let methods =
    List.map
    begin fun (id, tm : tmethod binding) ->
      id, {tm with body = cook_calls_of_block tm.body }
    end
    g.methods
  in

  { g with methods = methods }

let evaluate_globals (g : global_env) (es : texp_list) : global_env =
  let vs = List.map 
    (fun (i,(t,e)) -> i, (t, ref @@ snd @@ interp_exp {g;l=[];tid=None} e)) 
    es 
  in {g with globals = vs}

let time_servois = ref false

let initialize_env (prog : prog) (infer_phis : bool) =
  let g =
    { methods = []
    ; globals = []
    ; structs = []
    ; lib_methods = Vcylib.lib_methods
    ; group_commute = []
    }
  in
  (* Initialize environment *)
  let g, globals = construct_env g [] prog in
  let g = evaluate_globals g globals in
  let g = cook_calls g in
  let g = 
    if infer_phis
    then
      let dt, g =
        time_exec @@ fun () -> infer_phis_of_prog g
      in if !time_servois
      then Printf.eprintf "%f\n" dt; 
      g
    else g
  in
  (* let gc_list = interp_global_commute g in  *)
  if !dswp_mode then
    List.iter (fun m -> match m with | (Gmdecl {elt = {pure;mrtyp;mname;args;body}; loc = l}) -> Exe_pdg.ps_dswp body l args g globals | _ -> ()) prog;

  (* EK TODO - complain if more than 1 method declaraiton in SWP mode *)

  {g;l=[[[]]];tid=None}


let prepare_prog (prog : prog) (argv : string array) =
  (* Initialize environment *)
  let env = initialize_env prog true in

  (* Construct expressions representing argc and argv values *)
  let e_argc = CInt (Int64.of_int @@ Array.length argv) |> no_loc in
  let e_argv =
    let l = argv |> Array.map (fun v -> CStr v |> no_loc) |> Array.to_list in
    CArr (TStr, l) |> no_loc
  in
  (* Printf.printf "%s\n" (AstPP.string_of_exp e_argv); *)

  if !dswp_mode then begin
    (* No "main call" in DSWP mode. Instead augment env with argc/argv*)
    let blk_stk = ["argc",(TInt, ref (VInt(Int64.of_int @@ Array.length argv)));
                   "argv",(TArr(TStr),ref (VArr (TStr, argv |> Array.map (fun v -> VStr v))))] in
    let cstk = [blk_stk] in
    { env with l = cstk :: env.l }, CBool(false) |> no_loc
    (* senddep_extend_env env [(TInt,"argc",VInt(Int64.of_int @@ Array.length argv));
                            (TArr(TStr),"argv",VArr (TStr, argv |> Array.map (fun v -> VStr v)))] *)
    (* { g=env.g; l=}, e *)
  end else 
    (* Construct main function 'Call' expression *)
    let e = CallRaw (main_method_name, [e_argc;e_argv]) |> no_loc in
    env, e

let interp_tasks env0 decls init_task tasks : value =
  set_task_def tasks;
  (* create a job for each task with no deps_in -- REMOVED, just start job 0 in scheduler. *)
  (* let jobs = List.filter (fun task -> null task.deps_in (* && task.id <> 0 *)) !task_defs
    |> List.map (fun task -> {tid=task.id; env=env0}) in *)
  (* start the scheduler *)
  scheduler init_task env0 |> flatten_value_option

(* Kick off interpretation of progam. 
 * Build initial environment, construct argc and argv,
 * begin interpretation. *)
let interp_prog (prog : prog) (argv : string array) : int64 =
  let env, e = prepare_prog prog argv in
  (* Evaluate main function invocation *)
  match (if !dswp_mode
    then begin
      pool := Domainslib.Task.setup_pool ~num_domains:!pool_size () |> some;
      interp_tasks env !Exe_pdg.generated_decl_vars (Option.get !Exe_pdg.generated_init_task) !Exe_pdg.generated_tasks
      end
    else interp_exp env e |> snd) with
  | VInt ret -> ret
  | _ -> raise @@ TypeFailure (main_method_name ^ " function did not return int", Range.norange)


(* Execute but return lapsed time instead of program return *)
let interp_prog_time (prog : prog) (argv : string array) : float =
  let env, e = prepare_prog prog argv in
  Vcylib.suppress_print := true;
  if !dswp_mode then
    begin
      pool := Domainslib.Task.setup_pool ~num_domains:!pool_size () |> some;
      let dt, _ = time_exec @@ fun () ->  interp_tasks env !Exe_pdg.generated_decl_vars (Option.get !Exe_pdg.generated_init_task) !Exe_pdg.generated_tasks in
      dt
    end
  else
    let dt, _ = time_exec @@ fun () -> interp_exp env e in
    dt
  (*let t0 = Unix.gettimeofday () in
  ignore @@ interp_exp env e;
  let t1 = Unix.gettimeofday () in
  t1 -. t0*)
