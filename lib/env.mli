type t = Program.fn Base.Map.M(Program.Id).t

val empty : t

val add_exn :
  t ->
  name:string ->
  fn:Program.fn ->
  (string, Program.fn, Base.String.comparator_witness) Base.Map.t

val find : t -> name:string -> Program.fn option
