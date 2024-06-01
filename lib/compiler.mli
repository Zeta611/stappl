val gen_sym : unit -> string
val gen_vertex : unit -> string
val sub : Program.Exp.t -> string -> Program.Det_exp.t -> Program.Exp.t
val gather_functions : Program.program -> Env.t

exception Not_closed_observation

val compile''' : Env.t -> Pred.t -> Program.Exp.t -> Graph.t * Program.Det_exp.t
