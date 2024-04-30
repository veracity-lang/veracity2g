open Ast
open Ast_print
type taskid = int 

(* t_i can depend on a list of variables written by some predecessor t_j *)
type dependency = {
  pred_task: taskid;
  vars: (ty * id) list 
}

type exe_label = Doall | Sequential

type task = {
  id : taskid;
  deps_in : dependency list; (* a list of other tasks/vars that I depend on *)
  deps_out : dependency list; (* a list of other tasks/vars that I provide for *)
  body: block node;
  label: exe_label;
}

let str_of_vars_list (vlist : (ty * id) list) : string  = 
  (String.concat ";" (List.map (fun (t,i) -> 
       Printf.sprintf "%s %s" (AstML.string_of_ty t) i
  ) vlist))

let str_of_task_deps deplist = 
  "{"
  ^(String.concat "|" (List.map (fun dep ->
    Printf.sprintf "from %d: %s" dep.pred_task (str_of_vars_list dep.vars)
  ) deplist))
  ^"}"

let str_of_task tsk = 
    Printf.sprintf "{Task %d:\n  deps_in:%s\n  deps_out:%s\n  label:%s}"
      tsk.id (str_of_task_deps tsk.deps_in) (str_of_task_deps tsk.deps_out)
      (match tsk.label with | Doall -> "DOALL" | Sequential -> "Seq")

let rec calculate_semaphores tlist : (taskid * taskid) list =
  match tlist with 
  | [] -> []
  | (tk::rest) ->
      (List.map (fun dep -> (dep.pred_task,tk.id)) tk.deps_in )
      @ (calculate_semaphores rest)

(* things like t1_to_t2_x *)
let rec calculate_handoff_vars tlist : (ty * id * taskid * taskid) list =
  match tlist with 
  | [] -> []
  | (tk::rest) ->
      List.flatten (List.map (fun dep -> 
        (List.map (fun (t,x) -> (t,x,dep.pred_task,tk.id) ) dep.vars)
      ) tk.deps_in)
      @ (calculate_handoff_vars rest)
      
(*
Example:

task1:
  { id=1; deps_in:(task1,p); deps_out:[(task1,p->next);(task2,p);(task3,p)]
    body="id=p->id;if(!visited[id])visited[id]=true;"}

task2:
  { id=2; deps_in:(task1,p); deps_out:[]
    body="q=p->inner_list; .."}

task3:
  { id=3; deps_in:(task1,p); deps_out:[]
    body="q=p->inner_list; .."}
*)

let mk_int_dep pred_id var_id = {pred_task=pred_id; vars=[(TInt,var_id)]}

let example_var_decls () =
  [
    Gvdecl(no_loc { name="p"; ty=TInt; init=(no_loc (CInt 0L))})
  ]

let example_tasks () : task list = 
  [
    { id=1; 
      deps_in=[(mk_int_dep 1 "p")]; 
      deps_out=[(mk_int_dep 1 "pnext");(mk_int_dep 2 "p");(mk_int_dep 3 "p")];
      body=no_loc [(no_loc (Ret(None)))];
      label=Doall
    };
    { id=2; 
      deps_in=[(mk_int_dep 1 "p")]; 
      deps_out=[];
      body=no_loc [(no_loc (Ret(None)))];
      label=Doall
    };
    { id=3; 
      deps_in=[(mk_int_dep 1 "p")]; 
      deps_out=[];
      body=no_loc [(no_loc (Ret(None)))];
      label=Doall
    }
  ]
(* p= 0...maxp *)
(*
let test_var_decls = [
  { name = "p";    ty=TInt ; init=no_loc (Const 0) };
  { name = "pmax"; ty=TInt ; init=no_loc (Const 155) };
  { name = "id";   ty=TInt ; init=no_loc (Const 0) };
  { name = "ids";  ty=TArr TInt ; init=no_loc (NewArr(TInt, no_loc (Const 0))) };
]
let test_tasks = [
  { id=1; deps_in:(task1,p); deps_out:[(task1,p->next);(task2,p);(task3,p)]
    body= no_loc {[
      (* p = ...; id = ids[p]; if(!visited[id])visited[id]=1; *)
      Assn(no_loc , no_loc);
      If(no_loc , no_loc, no_loc )
    ]}

      elt: 
      loc: 
    }
    "id=p->id;if(!visited[id])visited[id]=true;"}
  ;
  { id=2; deps_in:(task1,p); deps_out:[]
    body="q=p->inner_list; .."}
  ;
  { id=3; deps_in:(task1,p); deps_out:[]
    body="q=p->inner_list; .."}
]
*)