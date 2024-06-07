open! Core
open Typed_tree

type env = any_v Id.Table.t

let rec eval : type a. env -> (a, det) texp -> a =
 fun env { ty; exp } ->
  match exp with
  | Value v -> v
  | Var x -> (
      let (Any (tv, v)) = Hashtbl.find_exn env x in
      match (ty, tv) with
      | Tyi, Tyi -> v
      | Tyr, Tyr -> v
      | Tyb, Tyb -> v
      | _ -> assert false)
  | Bop (op, te1, te2) -> op.f (eval env te1) (eval env te2)
  | Uop (op, te) -> op.f (eval env te)
  | If (te_pred, te_cons, te_alt) ->
      if eval env te_pred then eval env te_cons else eval env te_alt
  | Call (f, args) -> f.sampler (eval_args env args)

and eval_args : type a. env -> (a, det) args -> a vargs =
 fun env -> function
  | [] -> []
  | te :: tl -> (te.ty, eval env te) :: eval_args env tl

let rec eval_pmdf (env : env) (Any { ty; exp } : any_det) :
    (any_v -> float) * any_v =
  match exp with
  | If (te_pred, te_cons, te_alt) ->
      if eval env te_pred then eval_pmdf env (Any te_cons)
      else eval_pmdf env (Any te_alt)
  | Call (f, args) ->
      let pmdf (Any (ty', v) : any_v) =
        match (ty, ty') with
        | Tyi, Tyi -> f.log_pmdf (eval_args env args) v
        | Tyr, Tyr -> f.log_pmdf (eval_args env args) v
        | Tyb, Tyb -> f.log_pmdf (eval_args env args) v
        | _, _ -> assert false
      in
      (pmdf, Any (ty, eval env { ty; exp }))
  | _ -> (* not reachable *) assert false

let gibbs_sampling ~(num_samples : int) (graph : Graph.t) (query : any_det) :
    float array =
  (* Initialize the context with the observed values. Float conversion must
     succeed as observed variables do not contain free variables *)
  let default : type a. a ty -> a = function
    | Tyi -> 0
    | Tyr -> 0.0
    | Tyb -> false
  in
  let ctx = Id.Table.create () in
  let () =
    Map.iteri graph.obs_map ~f:(fun ~key ~data:(Any { ty; exp }) ->
        let data : any_v = Any (ty, eval ctx { ty; exp }) in
        Hashtbl.set ctx ~key ~data)
  in
  let unobserved = Graph.unobserved_vertices_pmdfs graph in
  let () =
    List.iter unobserved ~f:(fun (key, Any { ty; _ }) ->
        let data : any_v = Any (ty, default ty) in
        Hashtbl.set ctx ~key ~data)
  in

  (* Adapted from gibbs_sampling of Owl *)
  let a, b = (1000, 10) in
  let num_iter = a + (b * num_samples) in
  let samples = Array.create ~len:num_samples 0. in
  for i = 0 to num_iter - 1 do
    (* Gibbs step *)
    List.iter unobserved ~f:(fun (key, exp) ->
        let curr = Hashtbl.find_exn ctx key in
        let log_pmdf, cand = eval_pmdf ctx exp in

        (* metropolis-hastings update logic *)
        Hashtbl.set ctx ~key ~data:cand;
        let log_pmdf', _ = eval_pmdf ctx exp in
        let log_alpha = log_pmdf' curr -. log_pmdf cand in

        (* variables influenced by "name" *)
        let name_infl =
          Map.filteri graph.pmdf_map ~f:(fun ~key:name ~data:(Any { exp; _ }) ->
              Id.(name = key) || Set.mem (fv exp) key)
        in
        let log_alpha =
          Map.fold name_infl ~init:log_alpha ~f:(fun ~key:name ~data:exp acc ->
              let prob_w_cand =
                (fst (eval_pmdf ctx exp)) (Hashtbl.find_exn ctx name)
              in
              Hashtbl.set ctx ~key ~data:curr;
              let prob_wo_cand =
                (fst (eval_pmdf ctx exp)) (Hashtbl.find_exn ctx name)
              in
              Hashtbl.set ctx ~key ~data:cand;
              acc +. prob_w_cand -. prob_wo_cand)
        in

        let alpha = Float.exp log_alpha in
        let uniform = Owl.Stats.std_uniform_rvs () in
        if Float.(uniform > alpha) then Hashtbl.set ctx ~key ~data:curr);

    if i >= a && i mod b = 0 then
      let (Any query) = query in
      let query =
        match (query.ty, eval ctx query) with
        | Tyi, i -> float_of_int i
        | Tyr, r -> r
        | Tyb, b -> if b then 1.0 else 0.0
      in
      samples.((i - a) / b) <- query
  done;

  samples

let infer ?(filename : string = "out") ?(num_samples : int = 100_000)
    (graph : Graph.t) (query : any_det) : string =
  let samples = gibbs_sampling graph ~num_samples query in

  let filename = String.chop_suffix_if_exists filename ~suffix:".stp" in
  let plot_path = filename ^ ".png" in

  let open Owl_plplot in
  let h = Plot.create plot_path in
  Plot.set_title h (Printing.to_string query);
  let mat = Owl.Mat.of_array samples 1 num_samples in
  Plot.histogram ~h ~bin:50 mat;
  Plot.output h;
  plot_path
