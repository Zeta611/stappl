open! Core
open Program

exception Unknown_distribution of string

let sample (dist_name : string) (args : float list) : float =
  let open Owl.Stats in
  match (dist_name, args) with
  | "bernoulli", [ p ] -> Float.of_int (binomial_rvs ~p ~n:1)
  | "normal", [ mu; sigma ] -> gaussian_rvs ~mu ~sigma
  | "uniform", [ a; b ] -> uniform_rvs ~a ~b
  | "exponential", [ lambda ] -> exponential_rvs ~lambda
  | "gamma", [ shape; scale ] -> gamma_rvs ~shape ~scale
  | _ -> raise (Unknown_distribution dist_name)

type log_pmdf = float -> float

let get_log_pmdf (dist_name : string) (args : float list) : log_pmdf =
  let open Owl.Stats in
  match (dist_name, args) with
  | "bernoulli", [ p ] -> fun n -> binomial_logpdf (Int.of_float n) ~p ~n:1
  | "normal", [ mu; sigma ] -> gaussian_logpdf ~mu ~sigma
  | "uniform", [ a; b ] -> uniform_logpdf ~a ~b
  | "exponential", [ lambda ] -> exponential_logpdf ~lambda
  | "gamma", [ shape; scale ] -> gamma_logpdf ~shape ~scale
  | _ -> raise (Unknown_distribution dist_name)

let rec eval (ctx : Eval_ctx.t) (exp : Det_exp.t) : float =
  let ev2 f e1 e2 = f (eval ctx e1) (eval ctx e2) in
  match Det_exp.eval exp with
  | Int n -> float_of_int n
  | Real r -> r
  | Bool b -> if b then 1. else 0.
  | Var name ->
      (* It is an error for a variable to be free at this stage.
         It should be either observed or set from the sampling process *)
      Eval_ctx.find_exn ctx ~name
  | Add (e1, e2) -> ev2 ( +. ) e1 e2
  | Radd (e1, e2) -> ev2 ( +. ) e1 e2
  | Minus (e1, e2) -> ev2 ( -. ) e1 e2
  | Rminus (e1, e2) -> ev2 ( -. ) e1 e2
  | Mult (e1, e2) -> ev2 ( *. ) e1 e2
  | Rmult (e1, e2) -> ev2 ( *. ) e1 e2
  | Div (e1, e2) -> ev2 ( /. ) e1 e2
  | Rdiv (e1, e2) -> ev2 ( /. ) e1 e2
  | Neg e -> -.eval ctx e
  | Rneg e -> -.eval ctx e
  | Req (e1, e2) -> if Float.(eval ctx e1 = eval ctx e2) then 1. else 0.
  | Eq (e1, e2) -> if Float.(eval ctx e1 = eval ctx e2) then 1. else 0.
  | Noteq (e1, e2) -> if Float.(eval ctx e1 <> eval ctx e2) then 1. else 0.
  | Less (e1, e2) -> if Float.(eval ctx e1 < eval ctx e2) then 1. else 0.
  | Rless (e1, e2) -> if Float.(eval ctx e1 < eval ctx e2) then 1. else 0.
  | And (e1, e2) ->
      if Float.(eval ctx e1 <> 0. && eval ctx e2 <> 0.) then 1. else 0.
  | Or (e1, e2) ->
      if Float.(eval ctx e1 <> 0. || eval ctx e2 <> 0.) then 1. else 0.
  | Not e -> if Float.(eval ctx e = 0.) then 1. else 0.
  | Prim_call (fn, args) ->
      let evaled_args = List.map args ~f:(eval ctx) in
      sample fn evaled_args
  | If (pred, conseq, alt) ->
      if Float.(eval ctx pred <> 0.0) then eval ctx conseq else eval ctx alt
  | e -> failwith ("Unsupported expression " ^ Det_exp.to_string e)

let rec eval_pmdf (ctx : Eval_ctx.t) : Dist.exp -> log_pmdf * float = function
  | Dist_obj { dist; args; _ } ->
      let args = List.map args ~f:(eval ctx) in
      (get_log_pmdf dist args, sample dist args)
  | If_de (pred, conseq, alt) ->
      if Float.(eval ctx pred <> 0.0) then eval_pmdf ctx conseq
      else eval_pmdf ctx alt
  | If_pred (_, conseq, One) -> eval_pmdf ctx conseq

let gibbs_sampling ~(num_samples : int) (graph : Graph.t) (query : Det_exp.t) :
    float array =
  (* Initialize the context with the observed values. Float conversion must
     succeed as observed variables do not contain free variables *)
  let ctx = Eval_ctx.create () in
  let find_exn name = Eval_ctx.find_exn ctx ~name in
  Map.iteri graph.obs_map ~f:(fun ~key:name ~data:value ->
      Eval_ctx.set ctx ~name ~value:(Det_exp.to_float value));

  let unobserved = Graph.unobserved_vertices_pmdfs graph in
  List.iter unobserved ~f:(fun (name, _) -> Eval_ctx.set ctx ~name ~value:0.);

  (* Adapted from gibbs_sampling of Owl *)
  let a, b = (1000, 10) in
  let num_iter = a + (b * num_samples) in
  let samples = Array.create ~len:num_samples 0. in
  for i = 0 to num_iter - 1 do
    (* Gibbs step *)
    List.iter unobserved ~f:(fun (name, pmdf_exp) ->
        let curr = find_exn name in
        let log_pmdf, cand = eval_pmdf ctx pmdf_exp in

        (* metropolis-hastings update logic *)
        Eval_ctx.set ctx ~name ~value:cand;
        let log_pmdf', _ = eval_pmdf ctx pmdf_exp in
        let log_alpha = log_pmdf' curr -. log_pmdf cand in

        (* variables influenced by "name" *)
        let name_infl =
          Map.filteri graph.pmdf_map ~f:(fun ~key:name' ~data:pmdf_exp ->
              Id.(name' = name) || Set.mem (Dist.fv pmdf_exp) name)
        in
        let log_alpha =
          Map.fold name_infl ~init:log_alpha
            ~f:(fun ~key:name' ~data:pmdf_exp acc ->
              let prob_w_cand =
                (fst (eval_pmdf ctx pmdf_exp)) (find_exn name')
              in
              Eval_ctx.set ctx ~name ~value:curr;
              let prob_wo_cand =
                (fst (eval_pmdf ctx pmdf_exp)) (find_exn name')
              in
              Eval_ctx.set ctx ~name ~value:cand;
              acc +. prob_w_cand -. prob_wo_cand)
        in

        let alpha = Float.exp log_alpha in
        let uniform = Owl.Stats.std_uniform_rvs () in
        if Float.(uniform > alpha) then Eval_ctx.set ctx ~name ~value:curr);

    if i >= a && i mod b = 0 then samples.((i - a) / b) <- eval ctx query
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
