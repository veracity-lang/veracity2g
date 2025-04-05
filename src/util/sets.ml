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

  let union ((tbl1, m1) : 'd t) ((tbl2, m2) : 'd t) : 'd t =
    let result = make () in
    Mutex.protect m1 (fun () ->
      Hashtbl.iter (fun key _ -> Hashtbl.replace (fst result) key ()) tbl1);
    Mutex.protect m2 (fun () ->
      Hashtbl.iter (fun key _ -> Hashtbl.replace (fst result) key ()) tbl2);
    result

  (* Intersection of two sets *)
  let intersect ((tbl1, m1) : 'd t) ((tbl2, m2) : 'd t) : 'd t =
    let result = make () in
    Mutex.protect m1 (fun () ->
      Hashtbl.iter (fun key _ ->
        if Mutex.protect m2 (fun () -> Hashtbl.mem tbl2 key) then
          Hashtbl.replace (fst result) key ()
      ) tbl1);
    result
      

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

  let union (t1 : 'd t) (t2 : 'd t) : 'd t =
    let result = make () in
    Hashtbl.iter (fun key _ -> Hashtbl.replace result key ()) t1;
    Hashtbl.iter (fun key _ -> Hashtbl.replace result key ()) t2;
    result
    
  let intersect (t1 : 'd t) (t2 : 'd t) : 'd t =
    let result = make () in
    Hashtbl.iter (fun key _ ->
      if Hashtbl.mem t2 key then
        Hashtbl.replace result key ()
    ) t1;
    result
    

  let size = Hashtbl.length

end
