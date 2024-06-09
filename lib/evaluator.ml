open! Core
open Typed_tree

type query = det some_rv_texp

module Ctx = struct
  type t = some_val Id.Table.t

  let create = Id.Table.create
  let set ctx ~name ~value = Hashtbl.set ctx ~key:name ~data:value
  let find_exn = Hashtbl.find_exn
end

let rec eval_dat : type a s. Ctx.t -> ((a, s) dat_ty, det) texp -> a =
 fun ctx { ty; exp } ->
  match exp with
  | Value v -> v
  | Var x -> (
      let (Ex (tv, v)) = Ctx.find_exn ctx x in
      match eq_dtys (dty_of_dat_ty ty) tv with
      | Some Refl -> v
      | None -> assert false)
  | Bop ({ op; _ }, te1, te2) -> op (eval_dat ctx te1) (eval_dat ctx te2)
  | Uop ({ op; _ }, te) -> op (eval_dat ctx te)
  | If (te_pred, te_cons, te_alt) ->
      if eval_dat ctx te_pred then eval_dat ctx te_cons else eval_dat ctx te_alt
  | If_just te -> eval_dat ctx te

and eval_dist : type a. Ctx.t -> (a dist_ty, det) texp -> a =
 fun ctx { ty = Dist_ty dty as ty; exp } ->
  match exp with
  | Call (f, args) -> f.sampler (eval_args ctx args)
  | Var x -> (
      let (Ex (tv, v)) = Ctx.find_exn ctx x in
      match eq_dtys dty tv with Some Refl -> v | None -> assert false)
  | If_pred (pred, dist) ->
      if eval_pred ctx pred then eval_dist ctx dist
      else eval_dist ctx { ty; exp = Call (Dist.one dty, []) }

and eval_pred (ctx : Ctx.t) : pred -> bool =
  (*print_endline "[eval_pred]";*)
  function
  | Empty | True -> true
  | False -> false
  | And (p, de) -> eval_dat ctx de && eval_pred ctx p
  | And_not (p, de) -> (not (eval_dat ctx de)) && eval_pred ctx p

and eval_args : type a. Ctx.t -> (a, det) args -> a vargs =
 fun ctx -> function
  | [] -> []
  | ({ ty = Dat_ty (dty, _); _ } as te) :: tl ->
      (dty, eval_dat ctx te) :: eval_args ctx tl

let rec eval_pmdf :
    type a. Ctx.t -> (a dist_ty, det) texp -> (some_val -> real) * some_val =
 fun ctx { ty = Dist_ty dty as ty; exp } ->
  match exp with
  | If_pred (pred, te) ->
      if eval_pred ctx pred then eval_pmdf ctx te
      else eval_pmdf ctx { ty; exp = Call (Dist.one dty, []) }
  | Call (f, args) ->
      let pmdf (Ex (ty', v) : some_val) =
        match eq_dtys dty ty' with
        | Some Refl -> f.log_pmdf (eval_args ctx args) v
        | _ -> assert false
      in
      (pmdf, Ex (dty, eval_dist ctx { ty; exp }))
  | _ -> (* not reachable *) assert false

let gibbs_sampling ~(num_samples : int) (graph : Graph.t) (Ex query : query) :
    float array =
  (* Initialize the context with the observed values. Float conversion must
     succeed as observed variables do not contain free variables *)
  let default : type a. a dty -> a = function
    | Tyu -> ()
    | Tyb -> false
    | Tyi -> 0
    | Tyr -> 0.0
  in
  let ctx = Id.Table.create () in
  Map.iteri graph.obs_map
    ~f:(fun ~key:name ~data:(Ex { ty = Dat_ty (dty, _) as ty; exp }) ->
      let value : some_val = Ex (dty, eval_dat ctx { ty; exp }) in
      Ctx.set ctx ~name ~value);

  let unobserved = Graph.unobserved_vertices_pmdfs graph in
  List.iter unobserved ~f:(fun (name, Ex { ty = Dist_ty dty; _ }) ->
      let value : some_val = Ex (dty, default dty) in
      Ctx.set ctx ~name ~value);

  (* Adapted from gibbs_sampling of Owl *)
  let a, b = (1000, 10) in
  let num_iter = a + (b * num_samples) in
  let samples = Array.create ~len:num_samples 0. in
  for i = 0 to num_iter - 1 do
    (* Gibbs step *)
    List.iter unobserved ~f:(fun (name, Ex exp) ->
        let curr = Ctx.find_exn ctx name in
        let log_pmdf, cand = eval_pmdf ctx exp in

        (* metropolis-hastings update logic *)
        Ctx.set ctx ~name ~value:cand;
        let log_pmdf', _ = eval_pmdf ctx exp in
        let log_alpha = log_pmdf' curr -. log_pmdf cand in

        (* variables influenced by "name" *)
        let name_infl =
          Map.filteri graph.pmdf_map ~f:(fun ~key:name' ~data:(Ex { exp; _ }) ->
              Id.(name' = name) || Set.mem (fv exp) name)
        in
        let log_alpha =
          Map.fold name_infl ~init:log_alpha
            ~f:(fun ~key:name' ~data:(Ex exp) acc ->
              let prob_w_cand =
                (fst (eval_pmdf ctx exp)) (Ctx.find_exn ctx name')
              in
              Ctx.set ctx ~name ~value:curr;
              let prob_wo_cand =
                (fst (eval_pmdf ctx exp)) (Ctx.find_exn ctx name')
              in
              Ctx.set ctx ~name ~value:cand;
              acc +. prob_w_cand -. prob_wo_cand)
        in

        let alpha = Float.exp log_alpha in
        let uniform = Owl.Stats.std_uniform_rvs () in
        if Float.(uniform > alpha) then Ctx.set ctx ~name ~value:curr);

    if i >= a && i mod b = 0 then
      let query =
        match (dty_of_dat_ty query.ty, eval_dat ctx query) with
        | Tyu, _ -> 0.0
        | Tyb, b -> if b then 1.0 else 0.0
        | Tyi, i -> float_of_int i
        | Tyr, r -> r
      in
      samples.((i - a) / b) <- query
  done;

  samples

let infer ?(filename : string = "out") ?(num_samples : int = 100_000)
    (graph : Graph.t) (query : query) : string =
  let samples = gibbs_sampling graph ~num_samples query in

  let filename = String.chop_suffix_if_exists filename ~suffix:".stp" in
  let plot_path = filename ^ ".png" in

  let open Owl_plplot in
  let h = Plot.create plot_path in
  Plot.set_title h
    Typed_tree.Erased.([%sexp (of_rv query : exp)] |> Sexp.to_string);
  let mat = Owl.Mat.of_array samples 1 num_samples in
  Plot.histogram ~h ~bin:50 mat;
  Plot.output h;
  plot_path
