val gen_sym : unit -> Program.Id.t
val gen_vertex : unit -> string
val sub : Program.Exp.t -> Program.Id.t -> Program.Det_exp.t -> Program.Exp.t

exception Not_closed_observation

val compile : Env.t -> Pred.t -> Program.Exp.t -> Graph.t * Program.Det_exp.t
