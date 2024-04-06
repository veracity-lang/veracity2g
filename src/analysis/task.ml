
type taskid = int 

(* t_i can depend on a list of variables written by some predecessor t_j *)
type dependency = {
  pred_task: taskid;
  vars: string list 
}

type task = {
  id : taskid;
  deps_in : dependency list; (* a list of other tasks/vars that I depend on *)
  deps_out : dependency list; (* a list of other tasks/vars that I provide for *)
  body: stmt;
}

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