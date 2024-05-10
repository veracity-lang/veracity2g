type t = Thread.t

let create (f : unit -> unit) : t =
  Thread.create f ()

let join : t -> unit =
  Thread.join

let scheduler () = 
   failwith "todo - scheduler for parallel_singlecore"