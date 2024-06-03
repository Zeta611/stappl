open! Core
open Program

exception Unknown_distribution of string

let sample dist args =
  let open Owl.Stats in
  match (dist, args) with
  | "bernoulli", [ p ] -> if Float.(Random.float 1.0 < p) then 1.0 else 0.0
  | "normal", [ mu; sigma ] -> gaussian_rvs ~mu ~sigma
  | "uniform", [ a; b ] -> uniform_rvs ~a ~b
  | "exponential", [ lambda ] -> exponential_rvs ~lambda
  | "gamma", [ shape; scale ] -> gamma_rvs ~shape ~scale
  | _ -> raise (Unknown_distribution dist)

(*type value = Int of int | Real of float | Bool of bool*)

let rec eval (env : Infer_env.t) (exp : Det_exp.t) : float =
  let ev2 f e1 e2 = f (eval env e1) (eval env e2) in
  match Det_exp.eval exp with
  | Int n -> float_of_int n
  | Real r -> r
  | Var name -> (
      match Infer_env.find env ~name with
      | Some value -> value
      | None -> Random.float 1.0)
  | Add (e1, e2) -> ev2 ( +. ) e1 e2
  | Radd (e1, e2) -> ev2 ( +. ) e1 e2
  | Minus (e1, e2) -> ev2 ( -. ) e1 e2
  | Mult (e1, e2) -> ev2 ( *. ) e1 e2
  | Div (e1, e2) -> ev2 ( /. ) e1 e2
  | Prim_call (fn, args) ->
      let evaled_args = List.map args ~f:(eval env) in
      sample fn evaled_args
  | If (pred, conseq, alt) ->
      if Float.(eval env pred <> 0.0) then eval env conseq else eval env alt
  | Eq (e1, e2) -> if Float.(eval env e1 = eval env e2) then 1.0 else 0.0
  | e -> failwith ("Unsupported expression " ^ Det_exp.to_string e)

let rec eval_conditional (env : Infer_env.t) (cond : Dist.exp) =
  match cond with
  | Dist_obj { dist; args; _ } ->
      let evaluated_args = List.map args ~f:(eval env) in
      sample dist evaluated_args
  | If_de (pred, conseq, alt) ->
      if Float.(eval env pred <> 0.0) then eval_conditional env conseq
      else eval_conditional env alt
  | If_pred (_, conseq, One) -> eval_conditional env conseq

let gibbs_sampling (g : Graph.t) (initial_state : (Id.t * Det_exp.t) list)
    (num_iterations : int) (query : Det_exp.t) : float array =
  let samples = Array.create ~len:num_iterations 0.0 in
  let env =
    ref
      (List.fold initial_state ~init:Infer_env.empty
         ~f:(fun env (name, value) ->
           Infer_env.set env ~name ~value:(eval env value)))
  in
  for i = 0 to num_iterations - 1 do
    List.iter g.vertices ~f:(fun v ->
        if not (Map.mem g.obs_map v) then
          let new_value =
            match Map.find g.det_map v with
            | Some exp -> eval_conditional !env exp
            | None -> Random.float 1.0
          in
          env := Infer_env.set !env ~name:v ~value:new_value);
    samples.(i) <- eval !env query
  done;
  samples

let infer ~(filename : string) (graph : Graph.t) (query : Det_exp.t) : string =
  let num_iterations = 1000 in
  (* Use graph.obs_map in initialization*)
  let initial_state =
    List.map graph.vertices ~f:(fun v ->
        match Map.find graph.obs_map v with
        | Some obs_value -> (v, obs_value)
        | None -> (v, Det_exp.Var v))
  in
  let samples = gibbs_sampling graph initial_state num_iterations query in
  let open Owl_plplot in
  let plot_path = filename ^ ".png" in
  let h = Plot.create plot_path in
  Plot.set_title h "Query Distribution";
  let open Owl in
  let samples_matrix = Mat.of_array samples 1 num_iterations in
  Plot.histogram ~h ~bin:50 samples_matrix;
  Plot.output h;
  plot_path
