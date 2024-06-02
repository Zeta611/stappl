open! Core
open Program
open! Infer_env

let eval_with_infer_env (env : Infer_env.t) (exp : Det_exp.t) : float =
  let rec eval env exp =
    let evi f e1 e2 = f (eval env e1) (eval env e2)
    and evr f e1 e2 = f (eval env e1) (eval env e2) in
    let simplified_exp = Det_exp.eval exp in
    match simplified_exp with
    | Det_exp.Int n -> float_of_int n
    | Det_exp.Real r -> r
    | Det_exp.Var x -> (
        match Infer_env.find env x with
        | Some value -> value
        | None ->
            Random.float 1.0
            (*failwith (Printf.sprintf "Variable %s not found in environment in %s" x (Infer_env.to_string env)))*)
        )
    | Det_exp.Add (e1, e2) -> evi ( +. ) e1 e2
    | Det_exp.Radd (e1, e2) -> evr ( +. ) e1 e2
    | Det_exp.Minus (e1, e2) -> eval env e1 -. eval env e2
    | Det_exp.Mult (e1, e2) -> eval env e1 *. eval env e2
    | _ -> failwith "Unsupported expression"
  in
  eval env exp

let sample_from_dist dist args =
  match (dist, args) with
  | "bernoulli", [ p ] -> if Float.(Random.float 1.0 < p) then 1.0 else 0.0
  | "normal", [ mu; sigma ] -> Owl.Stats.gaussian_rvs ~mu ~sigma
  | "uniform", [ a; b ] -> Owl.Stats.uniform_rvs ~a ~b
  | "exponential", [ lambda ] -> Owl.Stats.exponential_rvs ~lambda
  | "gamma", [ shape; scale ] -> Owl.Stats.gamma_rvs ~shape ~scale
  | _ -> failwith ("Unsupported distribution: " ^ dist)

let gibbs_sampling (g : Graph.t) (initial_state : (Id.t * Det_exp.t) list)
    (num_iterations : int) (query : Det_exp.t) : float array =
  let samples = Array.create ~len:num_iterations 0.0 in
  let env =
    ref
      (List.fold initial_state ~init:Infer_env.empty ~f:(fun env (x, value) ->
           Infer_env.add env x (eval_with_infer_env env value)))
  in
  for i = 0 to num_iterations - 1 do
    List.iter g.vertices ~f:(fun v ->
        if not (Map.mem g.obs_map v) then
          let new_value =
            match Map.find g.det_map v with
            | Some (Dist_obj { dist; args; _ }) ->
                let evaluated_args =
                  List.map args ~f:(eval_with_infer_env !env)
                in
                sample_from_dist dist evaluated_args
            | Some (If_de (_, _, _)) -> failwith "If_de not supported"
            | Some (If_pred (_, _, _)) -> failwith "If_pred not supported"
            | None -> Random.float 1.0
          in
          env := Infer_env.add !env v new_value);
    samples.(i) <- eval_with_infer_env !env query
  done;
  samples

let infer (graph : Graph.t) (query : Det_exp.t) =
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
  let h = Plot.create "distribution.png" in
  Plot.set_title h "Query Distribution";
  let open Owl in
  let samples_matrix = Mat.of_array samples 1 num_iterations in
  Plot.histogram ~h ~bin:50 samples_matrix;
  Plot.output h
