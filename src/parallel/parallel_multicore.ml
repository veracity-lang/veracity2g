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
  tid: taskid;
  env: env;
  (* the environment will have in the stack the input variables:
  vals: (ty * id * value) list 
  exp will only be constants: CInt, CStr, CBool, etc
  *)
}

let schedule_task tsk ()

let job_queue = Queue.create ()

(* Interpreter calls this function at each SendDep to create a new job *)
let new_job j = Queue.add j job_queue

let scheduler poolsize task_list =
  (* Create a domain pool with four worker domains *)
  let pool = Task.setup_pool ~num_domains:poolsize () in

  (* create a function to quickly return a task by id *)
  let tid2task = List.fold_left (fun acc tsk -> 
        (fun tid -> if tsk.id == tid then tsk else (acc tid))
    ) (fun _ -> failwith "could not find task id") task_list in

  let run_job jb : unit = 
    interp_block jb.env (tid2task jb.tid).body 


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
          Task.async pool (fun () ->

              (* use doall information to have replicas of a task? *)

              Printf.printf "about to exec a new job for task %d)\n" j.tid;
              run_job j;

          loop ()
      | None -> ()
    in
    loop ()
  );

(*

  (* Task type representing work to be done *)
  type task = int -> unit
  
  (* A task generator function that generates tasks *)
  let task_generator (task_id : int) : task = fun _ ->
    Printf.printf "Task %d is being processed.\n" task_id;
    (* Simulate generating new tasks dynamically (by the current task) *)
    if task_id < 5 then
      Printf.printf "Task %d is generating new tasks.\n" task_id
  
  (* The main scheduler function *)
  let scheduler () =
    (* Create a domain pool with four worker domains *)
    let pool = Task.setup_pool ~num_domains:4 () in
    let tasks = Queue.create () in
  
    (* Initial tasks *)
    for i = 1 to 3 do
      Queue.add (task_generator i) tasks
    done;
  
    (* Process tasks from the queue *)
    Task.run pool (fun () ->
        let rec loop () =
          match Queue.take_opt tasks with
          | Some task ->
              Task.async pool (fun () ->
                  task 0;
                  (* Example: After task completes, add new tasks *)
                  Queue.add (task_generator (Random.int 100 + 1)) tasks);
              loop ()
          | None -> ()
        in
        loop ()
      );
  
    (* Wait for all tasks to finish *)
    Task.teardown_pool pool
  
  (* Entry point *)
  let () =
    Random.self_init ();
    scheduler ()
*)