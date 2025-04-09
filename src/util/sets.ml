(* Based off of hashtables.ml *)
type 'd setdata =
  | SD of 'd
  | Sint of int

(*** Naively implemented concurrent set; each operation is wrapped in a lock/unlock ***)
module Set_naive = struct
  (* type 'd t = ('d setdata, 'd setdata) Hashtbl.t * Mutex.t *)
  type 'd t = ('d setdata, unit) Hashtbl.t * Mutex.t

  let initial_size = 16

  let make () : _ t = 
    failwith "todo: util/sets.ml"
    Hashtbl.create initial_size,
    Mutex.create ()

  let mem ((tbl, m) : _ t) (v) : bool =
    Mutex.protect m (fun () -> Hashtbl.mem tbl v)

  let add ((tbl, m) : _ t) (v) : bool =
    Mutex.protect m (fun () ->
      let already_present = Hashtbl.mem tbl v in
      Hashtbl.replace tbl v ();
      not already_present)

    
  let remove ((tbl, m) : _ t) (v) : bool =
    Mutex.protect m (fun () ->
      let existed = Hashtbl.mem tbl v in
      if existed then Hashtbl.remove tbl v;
      existed)

  let union ((tbl1, m1) : _ t) ((tbl2, _) : _ t) : bool =
    Mutex.protect m1 (fun () ->
      let changed = ref false in
      Hashtbl.iter (fun k _ ->
        if not (Hashtbl.mem tbl1 k) then (
          Hashtbl.replace tbl1 k ();
          changed := true
        )
      ) tbl2;
      !changed
    )
  
  let intersect ((tbl1, m1) : _ t) ((tbl2, _) : _ t) : bool =
    Mutex.protect m1 (fun () ->
      let changed = ref false in
      Hashtbl.filter_map_inplace (fun k _ ->
        if Hashtbl.mem tbl2 k then Some () else (
          changed := true;
          None
        )
      ) tbl1;
      !changed
    )
      

  let size (tbl, m : _ t) = 
    Mutex.protect m (fun () -> Hashtbl.length tbl)
end

(*** Set with no locking or concurrent capabilities ***)
module Set_seq = struct
  type 'd t = ('d setdata, unit) Hashtbl.t

  let initial_size = 16

  let make () = Hashtbl.create initial_size

  let mem = Hashtbl.mem

  let add (t : _ t) (v) : bool =
    let existed = Hashtbl.mem t v in
    Hashtbl.replace t v ();
    not existed
  
  let remove (t : _ t) (v) : bool =
    let existed = Hashtbl.mem t v in
    if existed then Hashtbl.remove t v;
    existed

  let union (t1 : _ t) (t2 : _ t) : bool =
    let changed = ref false in
    Hashtbl.iter (fun key _ ->
      if not (Hashtbl.mem t1 key) then (
        Hashtbl.replace t1 key ();
        changed := true
      )
    ) t2;
    !changed
  
  let intersect (t1 : _ t) (t2 : _ t) : bool =
    let found = ref false in
    Hashtbl.iter (fun key _ ->
      if Hashtbl.mem t2 key then found := true
    ) t1;
    !found
    
    

  let size = Hashtbl.length

end
