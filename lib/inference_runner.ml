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

let rec eval (env : Infer_ctx.t) (exp : Det_exp.t) : float =
  let ev2 f e1 e2 = f (eval env e1) (eval env e2) in
  match Det_exp.eval exp with
  | Int n -> float_of_int n
  | Real r -> r
  | Var name -> (
      match Infer_ctx.find env ~name with
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

let rec eval_conditional (env : Infer_ctx.t) (cond : Dist.exp) =
  match cond with
  | Dist_obj { dist; args; _ } ->
      let evaluated_args = List.map args ~f:(eval env) in
      sample dist evaluated_args
  | If_de (pred, conseq, alt) ->
      if Float.(eval env pred <> 0.0) then eval_conditional env conseq
      else eval_conditional env alt
  | If_pred (_, conseq, One) -> eval_conditional env conseq

let gibbs_sampling ~(num_samples : int)
    ({ vertices; pmdf_map; obs_map; _ } : Graph.t) (query : Det_exp.t) :
    float array =
  (* Initialize the context with the observed values. Float conversion must
     succeed as observed variables do not contain free variables *)
  let ctx = Infer_ctx.create () in
  Map.iteri obs_map ~f:(fun ~key:name ~data:value ->
      Infer_ctx.set ctx ~name ~value:(Det_exp.to_float value));

  let unobserved_vertices =
    List.filter_map vertices ~f:(fun v ->
        if Map.mem obs_map v then None
        else
          let pmdf = Map.find_exn pmdf_map v in
          Some (v, pmdf))
  in

  (* Adapted from gibbs_sampling of Owl *)
  let a, b = (1000, 10) in
  let num_iter = a + (b * num_samples) in
  let samples = Array.create ~len:num_samples 0.0 in
  for i = 1 to num_iter - 1 do
    List.iter unobserved_vertices ~f:(fun (name, pmdf) ->
        let value = eval_conditional ctx pmdf in
        Infer_ctx.set ctx ~name ~value);
    if i >= a && i mod b = 0 then samples.((i - a) / b) <- eval ctx query
  done;

  samples

let infer ?(filename : string = "out") ?(num_samples : int = 1000)
    (graph : Graph.t) (query : Det_exp.t) : string =
  let samples = gibbs_sampling graph ~num_samples query in

  let filename = String.chop_suffix_if_exists filename ~suffix:".stp" in
  let plot_path = filename ^ ".png" in

  let open Owl_plplot in
  let h = Plot.create plot_path in
  Plot.set_title h "Query Distribution";
  let open Owl in
  let samples_matrix = Mat.of_array samples 1 num_samples in
  Plot.histogram ~h ~bin:50 samples_matrix;
  Plot.output h;
  plot_path
