(* Based off of hashtables.ml *)
type 'd setdata =
  | SD of 'd
  | Sint of int

(*** Naively implemented concurrent set; each operation is wrapped in a lock/unlock ***)
module Set_naive = struct
  type 'd t = ('d setdata, 'd setdata) Hashtbl.t * Mutex.t

  let initial_size = 16

  let make () : _ t = 
    failwith "todo: util/sets.ml"
    Hashtbl.create initial_size,
    Mutex.create ()

  let mem (tbl, m : _ t) k =
    Mutex.protect m (fun () -> Hashtbl.mem tbl k)

  let put (tbl, m : _ t) k v = 
    Mutex.protect m (fun () -> 
      let replaced = Hashtbl.mem tbl k in
      Hashtbl.replace tbl k v;
      replaced)

  let get (tbl, m : _ t) k = 
    Mutex.protect m (fun () -> Hashtbl.find_opt tbl k)

  let size (tbl, m : _ t) = 
    Mutex.protect m (fun () -> Hashtbl.length tbl)
end

(*** Set with no locking or concurrent capabilities ***)
module Set_seq = struct
  type 'd t = ('d setdata, 'd setdata) Hashtbl.t

  let initial_size = 16

  let make () = Hashtbl.create initial_size

  let mem = Hashtbl.mem

  let put t k v = 
    let replaced = mem t k in
    Hashtbl.replace t k v;
    replaced

  let get = Hashtbl.find_opt

  let size = Hashtbl.length

end
