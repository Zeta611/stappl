open! Core
open Program

exception Unknown_distribution of string

let sample dist args =
  let open Owl.Stats in
  match (dist, args) with
  | "bernoulli", [ p ] -> Float.of_int (binomial_rvs ~p ~n:1)
  | "normal", [ mu; sigma ] -> gaussian_rvs ~mu ~sigma
  | "uniform", [ a; b ] -> uniform_rvs ~a ~b
  | "exponential", [ lambda ] -> exponential_rvs ~lambda
  | "gamma", [ shape; scale ] -> gamma_rvs ~shape ~scale
  | _ -> raise (Unknown_distribution dist)

let rec eval (ctx : Eval_ctx.t) (exp : Det_exp.t) : float =
  let ev2 f e1 e2 = f (eval ctx e1) (eval ctx e2) in
  match Det_exp.eval exp with
  | Int n -> float_of_int n
  | Real r -> r
  | Var name ->
      (* It is an error for a variable to be free at this stage.
         It should be either observed or set from the sampling process *)
      Eval_ctx.find_exn ctx ~name
  | Add (e1, e2) -> ev2 ( +. ) e1 e2
  | Radd (e1, e2) -> ev2 ( +. ) e1 e2
  | Minus (e1, e2) -> ev2 ( -. ) e1 e2
  | Mult (e1, e2) -> ev2 ( *. ) e1 e2
  | Div (e1, e2) -> ev2 ( /. ) e1 e2
  | Prim_call (fn, args) ->
      let evaled_args = List.map args ~f:(eval ctx) in
      sample fn evaled_args
  | If (pred, conseq, alt) ->
      if Float.(eval ctx pred <> 0.0) then eval ctx conseq else eval ctx alt
  | Eq (e1, e2) -> if Float.(eval ctx e1 = eval ctx e2) then 1.0 else 0.0
  | e -> failwith ("Unsupported expression " ^ Det_exp.to_string e)

let rec eval_pmdf (ctx : Eval_ctx.t) : Dist.exp -> float = function
  | Dist_obj { dist; args; _ } ->
      let args = List.map args ~f:(eval ctx) in
      (*printf "%g\n" (List.hd_exn args);*)
      sample dist args
  | If_de (pred, conseq, alt) ->
      if Float.(eval ctx pred <> 0.0) then eval_pmdf ctx conseq
      else eval_pmdf ctx alt
  | If_pred (_, conseq, One) -> eval_pmdf ctx conseq

let gibbs_sampling ~(num_samples : int) (graph : Graph.t) (query : Det_exp.t) :
    float array =
  (* Initialize the context with the observed values. Float conversion must
     succeed as observed variables do not contain free variables *)
  let ctx = Eval_ctx.create () in
  Map.iteri graph.obs_map ~f:(fun ~key:name ~data:value ->
      Eval_ctx.set ctx ~name ~value:(Det_exp.to_float value));

  let unobserved = Graph.unobserved_vertices_pmdfs graph in

  (* Adapted from gibbs_sampling of Owl *)
  let a, b = (1000, 10) in
  let num_iter = a + (b * num_samples) in
  let samples = Array.create ~len:num_samples 0.0 in
  for i = 1 to num_iter - 1 do
    List.iter unobserved ~f:(fun (name, pmdf) ->
        let value = eval_pmdf ctx pmdf in
        Eval_ctx.set ctx ~name ~value);
    if i >= a && i mod b = 0 then
      samples.((i - a) / b) <- eval ctx query (* (Det_exp.Var "X2") *)
  done;

  samples

let infer ?(filename : string = "out") ?(num_samples : int = 100_000)
    (graph : Graph.t) (query : Det_exp.t) : string =
  let samples = gibbs_sampling graph ~num_samples query in

  let filename = String.chop_suffix_if_exists filename ~suffix:".stp" in
  let plot_path = filename ^ ".png" in

  let open Owl_plplot in
  let h = Plot.create plot_path in
  Plot.set_title h (Det_exp.to_string query);
  let mat = Owl.Mat.of_array samples 1 num_samples in
  Plot.histogram ~h ~bin:50 mat;
  Plot.output h;
  plot_path
