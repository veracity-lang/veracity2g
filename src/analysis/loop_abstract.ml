(* Counter-loop abstraction for commutativity verification.

   A commute block whose whole body is a loop over a pure iteration counter,

     while (i < n) { C1; i = i + 1; C2 }      or
     for (int i = e; i < n; i = i + 1) { C }

   is verified by checking a single iteration (the body without the
   increment) against the other block.  This is sound by induction: if one
   iteration commutes with the other block f under phi, then
   C;C;...;C;f == f;C;C;...;C by swapping f past one iteration at a time.
   When both blocks are counter loops, pairwise commutativity of the two
   bodies gives C1^n;C2^m == C2^m;C1^n the same way.  No idempotence check
   is needed because each iteration is swapped separately; that would only
   be needed if a single iteration were spliced into a larger block.

   The induction only goes through when
   - the iteration count is the same in both orders: the guard mentions only
     the counter and variables written by neither block, the counter is
     touched by nothing but its increment, and the other block does not
     mention it;
   - phi (and any precondition) still holds at every intermediate state,
     because the swaps happen there: no variable in it is written by either
     block;
   - an iteration cannot cut the loop short (no return or raise).

   The counter is simply dropped rather than havoc'd: it starts arbitrary
   anyway, and havocing it would let the two runs of the bowtie encoding
   pick different final values and report a spurious counterexample.

   The abstraction is one-directional: a counterexample to the single
   iteration need not be one to the whole loop, so the completeness
   (non-commutativity) check is meaningless once it has fired. *)

open Ast

module S = Set.Make (String)

let rec ids_of_exp (e : exp node) : S.t =
  match e.elt with
  | Id x -> S.singleton x
  | CNull _ | CBool _ | CInt _ | CStr _ | NewHashTable _ -> S.empty
  | CArr (_, es) | CallRaw (_, es) | Call (_, es) -> ids_of_exps es
  | NewArr (_, e) | Uop (_, e) | Proj (e, _) -> ids_of_exp e
  | Index (a, b) | Bop (_, a, b) | HeapAlloc (a, b) -> S.union (ids_of_exp a) (ids_of_exp b)
  | Ternary (a, b, c) -> S.union (ids_of_exp a) (S.union (ids_of_exp b) (ids_of_exp c))
  | CStruct (_, fs) -> ids_of_exps (List.map snd fs)
  (* Heap cells are named after the heap model arrays, so they collide with
     what [Spec_generator.loop_modified_vars] reports for heap writes. *)
  | HeapValue (a, b) ->
      S.union (S.of_list Spec_generator.heap_model_vars) (S.union (ids_of_exp a) (ids_of_exp b))
  | HDerefValue a | HDerefNext a ->
      S.union (S.of_list Spec_generator.heap_model_vars) (ids_of_exp a)
  | Exists (x, _, e) | Forall (x, _, e) -> S.remove x (ids_of_exp e)

and ids_of_exps es = List.fold_left (fun s e -> S.union s (ids_of_exp e)) S.empty es

let rec ids_of_block (b : block) : S.t =
  List.fold_left (fun s st -> S.union s (ids_of_stmt st)) S.empty b

and ids_of_stmt (s : stmt node) : S.t =
  match s.elt with
  | Assn (l, r) -> S.union (ids_of_exp l) (ids_of_exp r)
  | Decl (x, (_, e)) -> S.add x (ids_of_exp e)
  | Ret eo -> Option.fold ~none:S.empty ~some:ids_of_exp eo
  | SCallRaw (_, es) | SCall (_, es) -> ids_of_exps es
  | If (c, b1, b2) -> S.union (ids_of_exp c) (S.union (ids_of_block b1.elt) (ids_of_block b2.elt))
  | For (vds, eo, so, b) ->
      List.fold_left (fun s (x, (_, e)) -> S.add x (S.union s (ids_of_exp e)))
        (S.union (Option.fold ~none:S.empty ~some:ids_of_exp eo)
           (S.union (Option.fold ~none:S.empty ~some:ids_of_stmt so) (ids_of_block b.elt)))
        vds
  | While (c, inv, b) ->
      S.union (ids_of_exp c)
        (S.union (Option.fold ~none:S.empty ~some:ids_of_exp inv) (ids_of_block b.elt))
  | Raise e | Assert e | Assume e | Havoc e | Require e -> ids_of_exp e
  | Commute (_, _, bls, _, _) ->
      List.fold_left (fun s b -> S.union s (ids_of_block b.elt)) S.empty bls
  | SBlock (_, b) -> ids_of_block b.elt
  | SendDep _ | SendEOP _ -> S.empty

(* Does [p] hold of [e] or any expression nested in it? *)
let rec exists_exp (p : exp node -> bool) (e : exp node) : bool =
  p e ||
  let go = exists_exp p in
  match e.elt with
  | CNull _ | CBool _ | CInt _ | CStr _ | NewHashTable _ | Id _ -> false
  | CArr (_, es) | CallRaw (_, es) | Call (_, es) -> List.exists go es
  | NewArr (_, e) | Uop (_, e) | Proj (e, _) | HDerefValue e | HDerefNext e
  | Exists (_, _, e) | Forall (_, _, e) -> go e
  | Index (a, b) | Bop (_, a, b) | HeapAlloc (a, b) | HeapValue (a, b) -> go a || go b
  | Ternary (a, b, c) -> go a || go b || go c
  | CStruct (_, fs) -> List.exists (fun (_, e) -> go e) fs

let is_call (e : exp node) = match e.elt with Call _ | CallRaw _ -> true | _ -> false

(* Every call in a block, as (is_user_method, pure, args). *)
let rec calls_of_block (b : block) = List.concat_map calls_of_stmt b
and calls_of_stmt (s : stmt node) =
  let rec of_exp (e : exp node) =
    let here = match e.elt with
      | Call (MethodM (_, m), es) -> [ (true, m.pure, es) ]
      | Call (MethodL (_, m), es) -> [ (false, m.pure, es) ]
      | CallRaw (_, es) -> [ (true, false, es) ]
      | _ -> []
    in
    let sub = match e.elt with
      | CArr (_, es) | CallRaw (_, es) | Call (_, es) -> List.concat_map of_exp es
      | NewArr (_, e) | Uop (_, e) | Proj (e, _) | HDerefValue e | HDerefNext e
      | Exists (_, _, e) | Forall (_, _, e) -> of_exp e
      | Index (a, b) | Bop (_, a, b) | HeapAlloc (a, b) | HeapValue (a, b) -> of_exp a @ of_exp b
      | Ternary (a, b, c) -> of_exp a @ of_exp b @ of_exp c
      | CStruct (_, fs) -> List.concat_map (fun (_, e) -> of_exp e) fs
      | _ -> []
    in
    here @ sub
  in
  let of_opt = Option.fold ~none:[] ~some:of_exp in
  match s.elt with
  | Assn (l, r) -> of_exp l @ of_exp r
  | Decl (_, (_, e)) -> of_exp e
  | Ret eo -> of_opt eo
  | SCall (MethodM (_, m), es) -> (true, m.pure, es) :: List.concat_map of_exp es
  | SCall (MethodL (_, m), es) -> (false, m.pure, es) :: List.concat_map of_exp es
  | SCallRaw (_, es) -> (true, false, es) :: List.concat_map of_exp es
  | If (c, b1, b2) -> of_exp c @ calls_of_block b1.elt @ calls_of_block b2.elt
  | For (vds, eo, so, b) ->
      List.concat_map (fun (_, (_, e)) -> of_exp e) vds @ of_opt eo
      @ Option.fold ~none:[] ~some:calls_of_stmt so @ calls_of_block b.elt
  | While (c, inv, b) -> of_exp c @ of_opt inv @ calls_of_block b.elt
  | Raise e | Assert e | Assume e | Havoc e | Require e -> of_exp e
  | Commute (_, _, bls, _, _) -> List.concat_map (fun b -> calls_of_block b.elt) bls
  | SBlock (_, b) -> calls_of_block b.elt
  | SendDep _ | SendEOP _ -> []

let rec decls_of_block (b : block) : ty bindlist =
  List.concat_map (fun (s : stmt node) -> match s.elt with
    | Decl (x, (t, _)) -> [ (x, t) ]
    | If (_, b1, b2) -> decls_of_block b1.elt @ decls_of_block b2.elt
    | For (vds, _, _, b) -> List.map (fun (x, (t, _)) -> (x, t)) vds @ decls_of_block b.elt
    | While (_, _, b) | SBlock (_, b) -> decls_of_block b.elt
    | _ -> []) b

let rec escapes (b : block) : bool =
  List.exists (fun (s : stmt node) -> match s.elt with
    | Ret _ | Raise _ | Commute _ | SendDep _ | SendEOP _ -> true
    | If (_, b1, b2) -> escapes b1.elt || escapes b2.elt
    | For (_, _, _, b) | While (_, _, b) | SBlock (_, b) -> escapes b.elt
    | _ -> false) b

(* Variables a block may change.  Calls are opaque: a library call can mutate
   the contents of anything passed by reference, so a non-scalar argument
   counts as written; a user method may write anything, so we give up. *)
let writes_of_block (scalar : id -> bool) (b : block) : S.t option =
  let calls = calls_of_block b in
  if List.exists (fun (user, pure, _) -> user && not pure) calls then None
  else
    let by_ref =
      List.concat_map (fun (_, _, es) -> es) calls
      |> ids_of_exps |> S.filter (fun x -> not (scalar x))
    in
    match Spec_generator.loop_modified_vars b with
    | ws -> Some (S.union by_ref (S.of_list ws))
    | exception Failure _ -> None

let rec unwrap (b : block) : block =
  match b with
  | [ { elt = SBlock (_, inner); _ } ] -> unwrap inner.elt
  | _ -> b

(* [i = i + c], [i = c + i] or [i = i - c] for a constant [c]. *)
let increment_of (s : stmt node) : id option =
  let const e = match e.elt with CInt _ -> true | _ -> false in
  match s.elt with
  | Assn ({ elt = Id i; _ }, { elt = Bop ((Add | Sub), { elt = Id j; _ }, c); _ })
    when i = j && const c -> Some i
  | Assn ({ elt = Id i; _ }, { elt = Bop (Add, c, { elt = Id j; _ }); _ })
    when i = j && const c -> Some i
  | _ -> None

type counter_loop = {
  counter : id;
  guard   : exp node;
  body    : block;  (* one iteration, without the increment *)
}

(* Recognise a block that is nothing but a counter loop.  Only the shape is
   checked here; whether the counter is used for anything else, and whether
   the guard is stable, depends on the other block and is checked in
   [abstract]. *)
let counter_loop_of (b : block) : counter_loop option =
  let mentions i (s : stmt node) = S.mem i (ids_of_stmt s) in
  let split_increment i body =
    let incs, rest = List.partition (fun s -> increment_of s = Some i) body in
    match incs with
    | [ _ ] when not (List.exists (mentions i) rest) -> Some rest
    | _ -> None
  in
  match unwrap b with
  | [ { elt = While (guard, None, body); _ } ] ->
      (* The counter is whichever variable the body bumps exactly once. *)
      List.find_map (fun s ->
        match increment_of s with
        | Some i when S.mem i (ids_of_exp guard) ->
            Option.map (fun rest -> { counter = i; guard; body = rest })
              (split_increment i body.elt)
        | _ -> None) body.elt
  | [ { elt = For ([ (i, (_, init)) ], Some guard, Some step, body); _ } ]
    when increment_of step = Some i
      && S.mem i (ids_of_exp guard)
      && not (S.mem i (ids_of_exp init))
      && not (S.mem i (ids_of_block body.elt)) ->
      Some { counter = i; guard; body = body.elt }
  | _ -> None

(* Replace each counter-loop block with a single iteration, when that is
   sound.  Returns the (possibly unchanged) blocks and the counters whose
   loops were abstracted; an empty list means nothing changed. *)
let abstract ~(globals : ty bindlist) ~(cv : commute_variant)
    ~(phi : exp node) ~(pre : exp node option) ~(post : exp node option)
    (blks : block node list) : block node list * id list =
  let unchanged = (blks, []) in
  let loops = List.map (fun b -> counter_loop_of b.elt) blks in
  let ctx_variant = match cv with CommuteVarLMCtx _ | CommuteVarRMCtx _ -> true | _ -> false in
  if List.for_all Option.is_none loops || ctx_variant || Option.is_some post then unchanged
  else
    let tys = globals @ List.concat_map (fun b -> decls_of_block b.elt) blks in
    let scalar x = match List.assoc_opt x tys with
      | Some (TInt | TBool | TStr) -> true
      | _ -> false
    in
    match List.map (fun b -> writes_of_block scalar b.elt) blks with
    | ws when List.mem None ws -> unchanged
    | ws ->
      let written = List.fold_left (fun acc w -> S.union acc (Option.get w)) S.empty ws in
      let conds = phi :: Option.to_list pre in
      let stable e = S.disjoint (ids_of_exp e) written && not (exists_exp is_call e) in
      let others_mention i k =
        List.exists (fun (j, b) -> j <> k && S.mem i (ids_of_block b.elt))
          (List.mapi (fun j b -> (j, b)) blks)
      in
      let ok k = function
        | None -> true
        | Some l ->
            let guard_rest = S.remove l.counter (ids_of_exp l.guard) in
            S.disjoint guard_rest written
            && not (exists_exp is_call l.guard)
            && not (others_mention l.counter k)
            && not (List.exists (fun c -> S.mem l.counter (ids_of_exp c)) conds)
            && not (escapes l.body)
      in
      if not (List.for_all stable conds && List.for_all Fun.id (List.mapi ok loops))
      then unchanged
      else
        List.map2 (fun b l -> match l with
          | None -> b
          | Some l -> node_up b l.body) blks loops,
        List.filter_map (Option.map (fun l -> l.counter)) loops

(* Constant-trip-count unrolling.

     x = c0;  ...;  while (x < n) { ...; x = x + c; ... }

   with c0, n and c > 0 integer literals runs exactly ceil((n - c0) / c)
   times (or zero), so it can be replaced by that many copies of its body.
   Unlike [abstract] this is exact, so the completeness check still means
   what it says, and it works for a loop anywhere in a block, not only one
   that makes up the whole block.

   The count is only known if, between the initialisation and the loop,
   nothing writes x (no impure user method call, which might), and inside
   the body x is written only by its single top-level increment.  Bodies
   that may [return] or [raise] are left alone. *)

let unroll_limit = 128

let const_int (e : exp node) = match e.elt with CInt n -> Some n | _ -> None

(* [x = c] or [T x = c]. *)
let const_init_of (s : stmt node) : (id * int64) option =
  match s.elt with
  | Assn ({ elt = Id x; _ }, e) | Decl (x, (_, e)) ->
      Option.map (fun n -> (x, n)) (const_int e)
  | _ -> None

(* [x = x + c] or [x = c + x] with a literal c > 0. *)
let positive_step_of (s : stmt node) : (id * int64) option =
  let pos e = match const_int e with Some c when c > 0L -> Some c | _ -> None in
  let step i c = Option.map (fun c -> (i, c)) (pos c) in
  match s.elt with
  | Assn ({ elt = Id i; _ }, { elt = Bop (Add, { elt = Id j; _ }, c); _ }) when i = j -> step i c
  | Assn ({ elt = Id i; _ }, { elt = Bop (Add, c, { elt = Id j; _ }); _ }) when i = j -> step i c
  | _ -> None

(* The loop runs while [x < bound] (exclusive bound). *)
let exclusive_bound_of (x : id) (guard : exp node) : int64 option =
  match guard.elt with
  | Bop (Lt, { elt = Id y; _ }, n) when y = x -> const_int n
  | Bop (Gt, n, { elt = Id y; _ }) when y = x -> const_int n
  | Bop (Lte, { elt = Id y; _ }, n) when y = x -> Option.map Int64.succ (const_int n)
  | Bop (Gte, n, { elt = Id y; _ }) when y = x -> Option.map Int64.succ (const_int n)
  | _ -> None

(* None when the writes cannot be determined. *)
let writes (b : block) : S.t option =
  match Spec_generator.loop_modified_vars b with
  | ws -> Some (S.of_list ws)
  | exception Failure _ -> None

let calls_impure_method (b : block) =
  List.exists (fun (user, pure, _) -> user && not pure) (calls_of_block b)

(* The interpreter gives every iteration its own scope, but the copies are
   inlined into one sequence, so a declaration in one copy stays visible in
   the next copy and after the loop.  That is harmless exactly when no name
   the body declares can mean anything else: each is declared once, at the
   top level of the body, is not mentioned before its declaration, and is
   not mentioned anywhere in the block outside the loop ([outside]).  A body
   that redeclares an outer variable (say [y = y + 1; int y = 0;]) is not
   unrolled. *)
let scoping_ok (outside : S.t) (body : block) : bool =
  let declared = List.map fst (decls_of_block body) in
  let top_decl x (s : stmt node) = match s.elt with Decl (y, _) -> y = x | _ -> false in
  List.length declared = S.cardinal (S.of_list declared)
  && List.for_all (fun x ->
       not (S.mem x outside)
       && match List.find_index (top_decl x) body with
          | None -> false
          | Some i -> List.for_all (fun s -> not (S.mem x (ids_of_stmt s)))
                        (List.filteri (fun j _ -> j < i) body))
     declared

(* The number of iterations of [while (guard) body] when x = c0 on entry. *)
let trip_count (known : (id * int64) list) (outside : S.t)
    (guard : exp node) (body : block) : (id * int) option =
  List.find_map (fun s ->
    match positive_step_of s with
    | None -> None
    | Some (x, c) ->
      match List.assoc_opt x known, exclusive_bound_of x guard with
      | Some c0, Some n ->
          let rest = List.filter (fun s' -> s' != s) body in
          let x_written_elsewhere = match writes rest with
            | Some ws -> S.mem x ws
            | None -> true
          in
          if List.length rest <> List.length body - 1
             || x_written_elsewhere || escapes body || calls_impure_method rest
             || not (scoping_ok outside body)
          then None
          else
            let span = Int64.sub n c0 in
            let k = if span <= 0L then 0L else Int64.(div (add span (sub c 1L)) c) in
            if k > Int64.of_int unroll_limit then None else Some (x, Int64.to_int k)
      | _ -> None) body

(* Unroll every such loop in a block, including nested ones.  [known] maps
   variables to the literal they were last set to on every path here;
   [outside] holds every name mentioned in the enclosing commute block
   outside this block.  Returns the new block and the (counter, iterations)
   of each loop unrolled. *)
let rec unroll_block (known : (id * int64) list) (outside : S.t) (b : block)
  : block * (id * int) list =
  let rec go known before = function
    | [] -> [], []
    | (s : stmt node) :: tl ->
      (* Everything in this block except [s] counts as outside for [s]. *)
      let outside_s = S.union outside (S.union before (ids_of_block tl)) in
      let forget ws known = match ws with
        | Some ws -> List.filter (fun (x, _) -> not (S.mem x ws)) known
        | None -> []
      in
      let loop_body guard inv body =
        let outside_b = S.union outside_s
            (S.union (ids_of_exp guard) (Option.fold ~none:S.empty ~some:ids_of_exp inv)) in
        unroll_block [] outside_b body.elt
      in
      let s', here, known' =
        match s.elt with
        | While (guard, None, body) ->
          let body', inner = loop_body guard None body in
          begin match trip_count known outside_s guard body.elt with
          | Some (x, k) ->
            let copies = List.init k (fun _ -> node_up s (SBlock (None, node_up body body'))) in
            copies, (x, k) :: inner,
            forget (Option.map (S.add x) (writes body.elt)) known
          | None ->
            [ node_up s (While (guard, None, node_up body body')) ], inner,
            forget (writes body.elt) known
          end
        | While (guard, Some inv, body) ->
          let body', inner = loop_body guard (Some inv) body in
          [ node_up s (While (guard, Some inv, node_up body body')) ], inner,
          forget (writes body.elt) known
        | If (c, b1, b2) ->
          let o1 = S.union outside_s (S.union (ids_of_exp c) (ids_of_block b2.elt)) in
          let o2 = S.union outside_s (S.union (ids_of_exp c) (ids_of_block b1.elt)) in
          let b1', u1 = unroll_block known o1 b1.elt in
          let b2', u2 = unroll_block known o2 b2.elt in
          [ node_up s (If (c, node_up b1 b1', node_up b2 b2')) ], u1 @ u2,
          forget (writes [ s ]) known
        | SBlock (l, inner) ->
          let inner', u = unroll_block known outside_s inner.elt in
          [ node_up s (SBlock (l, node_up inner inner')) ], u, forget (writes [ s ]) known
        | _ -> [ s ], [], forget (writes [ s ]) known
      in
      let known' = if calls_impure_method [ s ] then [] else known' in
      let known' = match const_init_of s with
        | Some (x, n) -> (x, n) :: List.remove_assoc x known'
        | None -> known'
      in
      let tl', rest = go known' (S.union before (ids_of_stmt s)) tl in
      s' @ tl', here @ rest
  in
  go known S.empty b

let unroll (blks : block node list) : block node list * (id * int) list =
  let pairs = List.map (fun b -> let b', u = unroll_block [] S.empty b.elt in node_up b b', u) blks in
  List.map fst pairs, List.concat_map snd pairs

(* The encoder inlines nested blocks and if-branches into the statements
   after them (Spec_generator.compile_block_to_smt), but the interpreter
   ends their scope there.  So a name declared inside one must not be used
   afterwards except after a fresh declaration of its own: such a use means
   an outer variable that the inlined declaration would shadow.  Reject the
   block rather than encode a different program. *)
let check_scopes (blks : block node list) : unit =
  (* The statements as the encoder sees them: nested blocks inlined. *)
  let rec flat (b : block) = List.concat_map (fun (s : stmt node) ->
    match s.elt with SBlock (_, inner) -> flat inner.elt | _ -> [ s ]) b in
  let used_after x (after : block) =
    match List.find_opt (fun s -> S.mem x (ids_of_stmt s)) (flat after) with
    | None -> false
    | Some { elt = Decl (y, (_, e)); _ } -> not (y = x && not (S.mem x (ids_of_exp e)))
    | Some _ -> true
  in
  let rec go (b : block) = match b with
    | [] -> ()
    | (s : stmt node) :: tl ->
      let scope (inner : block node) =
        List.iter (fun (x, _) ->
          if used_after x tl then
            failwith (Printf.sprintf
              "%s: %s is declared in this nested scope and used after it, where \
               it means another variable; rename one of them"
              (Range.string_of_range inner.loc) x))
          (decls_of_block inner.elt);
        go inner.elt
      in
      (match s.elt with
       | SBlock (_, inner) -> scope inner
       | If (_, b1, b2) -> scope b1; scope b2
       | While (_, _, body) | For (_, _, _, body) -> go body.elt
       | _ -> ());
      go tl
  in
  List.iter (fun b -> go b.elt) blks
