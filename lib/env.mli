type t = Program.fn Base.Map.M(Program.Id).t

val empty : t

val add :
  t ->
  name:string ->
  fn:Program.fn ->
  (string, Program.fn, Base.String.comparator_witness) Base.Map.t
  Base.Map.Or_duplicate.t

val find_exn : t -> name:string -> Program.fn
