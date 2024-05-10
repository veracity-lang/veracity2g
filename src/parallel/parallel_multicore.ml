open Ast

type t = unit Domain.t

let create : (unit -> unit) -> t =
  Domain.spawn

let join : t -> unit =
  Domain.join

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

(* let schedule_task tsk () *)

let task_defs = ref []
let set_task_def tlist = task_defs := tlist
let load_task_def taskid : task = 
  try List.find (fun t -> t.id == taskid) !task_defs
  with Not_found -> failwith "could not find task id"

let job_queue = Queue.create ()

(* Interpreter calls this function at each SendDep to create a new job *)
let new_job t e = Queue.add {tid=t; env=e} job_queue

let scheduler poolsize task_list : unit =
  (* Create a domain pool with four worker domains *)
  let pool = Task.setup_pool ~num_domains:poolsize () in

  (* create a function to quickly return a task by id *)
  (* let tid2task = List.fold_left (fun acc tsk -> 
        (fun tid -> if tsk.id == tid then tsk else (acc tid))
    ) (fun _ -> failwith "could not find task id") task_list in *)

  let run_job jb : unit = 
    interp_block jb.env (load_task_def jb.tid).body 
  in

     (* env = local callstack and globals *)
     (* 1. how do we make sure that mutation to shared vars? *)
     (* 2. how do we extend env to include the input vals? *)
       
    (* Idea:
        all variables are by default global.
        at the beginning of a task, input dependences are local.
        interp a variable,
       *)

        (* what about accuulated senddeps that need to become new jobs? *)


  Task.run pool (fun () ->
    let rec loop () =
      match Queue.take_opt job_queue with
      | Some j ->
          begin 
            Task.async pool (fun () ->
              (* use doall information to have replicas of a task? *)
              Printf.printf "about to exec a new job for task %d\n" j.tid;
              run_job j);
            loop ()
          end
      | None -> 
          ignore(Printf.printf "scheduler: reached an empty queue. need to now wait to join!")
    in
    loop ()
  )