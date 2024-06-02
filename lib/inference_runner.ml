open! Core
open Program

let sample_from_dist dist args =
  match (dist, args) with
  | "bernoulli", [ p ] -> if Float.(Random.float 1.0 < p) then 1.0 else 0.0
  | "normal", [ mu; sigma ] -> Owl.Stats.gaussian_rvs ~mu ~sigma
  | "uniform", [ a; b ] -> Owl.Stats.uniform_rvs ~a ~b
  | "exponential", [ lambda ] -> Owl.Stats.exponential_rvs ~lambda
  | "gamma", [ shape; scale ] -> Owl.Stats.gamma_rvs ~shape ~scale
  | _ -> failwith ("Unsupported distribution: " ^ dist)

let eval_with_infer_env (env : Infer_env.t) (exp : Det_exp.t) : float =
  let rec eval env exp =
    let evi f e1 e2 = f (eval env e1) (eval env e2)
    and evr f e1 e2 = f (eval env e1) (eval env e2) in
    let simplified_exp = Det_exp.eval exp in
    match simplified_exp with
    | Det_exp.Int n -> float_of_int n
    | Det_exp.Real r -> r
    | Det_exp.Var name -> (
        match Infer_env.find env ~name with
        | Some value -> value
        | None ->
            Random.float 1.0
            (*failwith (Printf.sprintf "Variable %s not found in environment in %s" x (Infer_env.to_string env)))*)
        )
    | Det_exp.Add (e1, e2) -> evi ( +. ) e1 e2
    | Det_exp.Radd (e1, e2) -> evr ( +. ) e1 e2
    | Det_exp.Minus (e1, e2) -> eval env e1 -. eval env e2
    | Det_exp.Mult (e1, e2) -> eval env e1 *. eval env e2
    | Det_exp.Div (e1, e2) -> eval env e1 /. eval env e2
    | Det_exp.Prim_call (fn, args) ->
        let evaled_args = List.map args ~f:(eval env) in
        sample_from_dist fn evaled_args
    | Det_exp.If (pred, conseq, alt) ->
        if Float.(eval env pred <> 0.0) then eval env conseq else eval env alt
    | Det_exp.Eq (e1, e2) ->
        if Float.(eval env e1 = eval env e2) then 1.0 else 0.0
    | _ ->
        failwith
          (sprintf "Unsupported expression %s"
             (Det_exp.to_string simplified_exp))
  in
  eval env exp

let rec eval_conditional (env : Infer_env.t) (cond : Dist.exp) =
  match cond with
  | Dist_obj { dist; args; _ } ->
      let evaluated_args = List.map args ~f:(eval_with_infer_env env) in
      sample_from_dist dist evaluated_args
  | If_de (pred, conseq, alt) ->
      if Float.(eval_with_infer_env env pred <> 0.0) then
        eval_conditional env conseq
      else eval_conditional env alt
  | If_pred (_, conseq, One) -> eval_conditional env conseq

let gibbs_sampling (g : Graph.t) (initial_state : (Id.t * Det_exp.t) list)
    (num_iterations : int) (query : Det_exp.t) : float array =
  let samples = Array.create ~len:num_iterations 0.0 in
  let env =
    ref
      (List.fold initial_state ~init:Infer_env.empty
         ~f:(fun env (name, value) ->
           Infer_env.set env ~name ~value:(eval_with_infer_env env value)))
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
    samples.(i) <- eval_with_infer_env !env query
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
