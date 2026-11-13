open Ast
open Dswp_task

(* When a job may skip (overtake) an earlier job whose commutativity condition
   holds.  Selected with --overtake.

   Any            skip whenever the condition holds, whether the other job is
                  waiting, running or done.  The old scheduler; unsound.
   Not_started    skip only a job that has not started (the Rocq rule until
                  2026-11-12; SC_DepElim now also admits running jobs).
   Hybrid         as Not_started, except that a condition that reads only
                  parameters and variables no task writes may also skip a
                  running job: nothing it reads can change while that job runs.
   Hybrid_locked  as Hybrid, except that a condition that reads written state
                  may skip a running job until that job's first write to a
                  variable some condition reads.  The condition is evaluated
                  under the job's guard, which the job takes to mark itself
                  dirty, so the job cannot reach that write in the meantime.
                  The default.

   Under every rule but Any, a job that overtook others re-checks before its
   first step (Rocq SC_Local, still_ok; Interp.recheck), unless --no-recheck.
   Any keeps the old behaviour and does not re-check.  The re-check is what
   the Rocq proof relies on; the rules above only decide when to stop waiting. *)
type rule = Any | Not_started | Hybrid | Hybrid_locked

let rule = ref Hybrid_locked

let recheck_disabled = ref false
let recheck () = !rule <> Any && not !recheck_disabled

let rule_names =
  ["any", Any; "not-started", Not_started; "hybrid", Hybrid; "hybrid-locked", Hybrid_locked]

let set_rule s =
  match List.assoc_opt s rule_names with
  | Some r -> rule := r
  | None -> raise (Arg.Bad ("--overtake: unknown rule " ^ s))

(* Variables an expression reads, apart from those it binds. *)
let rec reads (e : exp node) : id list =
  match e.elt with
  | Id x -> [x]
  | Exists (x, _, b) | Forall (x, _, b) -> List.filter (( <> ) x) (reads b)
  | _ -> List.concat_map reads (Wellformed.sub_exps e)

(* What a condition reads besides the parameters of its two instances. *)
let shared_reads (c : commute_condition) : id list =
  match c.condition with
  | None -> []
  | Some phi ->
    List.sort_uniq compare (reads phi)
    |> List.filter (fun x ->
      not (List.mem x c.my_task_formals || List.mem x c.other_task_formals))

(* Variables that some task assigns, and those that some condition reads
   besides parameters; set by prepare. *)
let written : id list ref = ref []
let cond_vars : id list ref = ref []

(* The written variables a condition reads.  Empty means that no job can
   change the condition's value while it runs. *)
let reads_written (c : commute_condition) : id list =
  List.filter (fun x -> List.mem x !written) (shared_reads c)

(* Whether a condition reads no variable at all, so that it has the same
   value for every pair of jobs; None (no condition) counts as constant. *)
let constant (c : commute_condition) : bool =
  match c.condition with None -> true | Some phi -> reads phi = []

let dirty_marker = "__phi_dirty"

(* Put the dirty marker before every statement that may assign a variable in
   watched, looking inside conditionals, loops and blocks. *)
let rec guard_block g watched (b : block node) : block node =
  node_up b (List.concat_map (guard_stmt g watched) b.elt)

and guard_stmt g watched (s : stmt node) : stmt node list =
  let hit = List.exists (fun (x, _) -> List.mem x watched) in
  let mark = node_up s (SCallRaw (dirty_marker, [])) in
  let exp_mark e = if hit (Wellformed.writes_of_exp g [] [] e) then [mark] else [] in
  let gb = guard_block g watched in
  match s.elt with
  | If (e, b1, b2) -> exp_mark e @ [node_up s (If (e, gb b1, gb b2))]
  | While (e, inv, b) -> exp_mark e @ [node_up s (While (e, inv, gb b))]
  | SBlock (l, b) -> [node_up s (SBlock (l, gb b))]
  | _ -> if hit (Wellformed.writes_of_block g [] [] [s]) then [mark; s] else [s]

(* Classify the conditions and, under Hybrid_locked, add the dirty markers to
   each task that a condition reading written state may have to skip. *)
let prepare (g : global_env) (tasks : dswp_task list) : dswp_task list =
  written := List.concat_map (fun t ->
    List.map fst (Wellformed.writes_of_block g [] [] t.body.elt)) tasks
    |> List.sort_uniq compare;
  cond_vars := List.concat_map (fun t ->
    List.concat_map (fun d -> shared_reads d.commute_cond) t.deps_in) tasks
    |> List.sort_uniq compare;
  if !rule <> Hybrid_locked then tasks
  else List.map (fun t ->
    let watched = List.concat_map (fun t' ->
      List.concat_map (fun d ->
        if d.pred_task = t.id then reads_written d.commute_cond else [])
        t'.deps_in) tasks in
    if watched = [] then t else { t with body = guard_block g watched t.body })
    tasks

(* One line per condition, for --job-stats. *)
let describe (tasks : dswp_task list) : string list =
  List.concat_map (fun t -> List.filter_map (fun d ->
    match d.commute_cond.condition with
    | None -> None
    | Some phi ->
      Some (Printf.sprintf "Condition at %s: %s" (Range.string_of_range phi.loc)
        (match reads_written d.commute_cond with
         | [] -> "reads no written state"
         | xs -> "reads written state (" ^ String.concat ", " xs ^ ")")))
    t.deps_in) tasks
  |> List.sort_uniq compare
