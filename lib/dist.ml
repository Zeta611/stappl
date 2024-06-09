open! Core
open Typed_tree

type some_dist = Ex : _ dist -> some_dist

let one : type a. a dty -> (a, unit) dist = function
  | Tyu ->
      {
        ret = Tyu;
        name = "one";
        params = [];
        sampler = (fun [] -> ());
        log_pmdf = (fun [] _ -> 0.0);
      }
  | Tyi ->
      {
        ret = Tyi;
        name = "one";
        params = [];
        sampler = (fun [] -> 1);
        log_pmdf = (fun [] _ -> 0.0);
      }
  | Tyr ->
      {
        ret = Tyr;
        name = "one";
        params = [];
        sampler = (fun [] -> 1.0);
        log_pmdf = (fun [] _ -> 0.0);
      }
  | Tyb ->
      {
        ret = Tyb;
        name = "one";
        params = [];
        sampler = (fun [] -> true);
        log_pmdf = (fun [] _ -> 0.0);
      }

let get_dist (name : Id.t) : some_dist =
  let open Owl.Stats in
  match name with
  | "bernoulli" ->
      Ex
        {
          ret = Tyb;
          name = "bernoulli";
          params = [ Tyr ];
          sampler = (fun [ (Tyr, p) ] -> binomial_rvs ~p ~n:1 = 1);
          log_pmdf =
            (fun [ (Tyr, p) ] b -> binomial_logpdf ~p ~n:1 (Bool.to_int b));
        }
  | "normal" ->
      Ex
        {
          ret = Tyr;
          name = "normal";
          params = [ Tyr; Tyr ];
          sampler = (fun [ (Tyr, mu); (Tyr, sigma) ] -> gaussian_rvs ~mu ~sigma);
          log_pmdf =
            (fun [ (Tyr, mu); (Tyr, sigma) ] -> gaussian_logpdf ~mu ~sigma);
        }
  | _ -> failwith "Unknown primitive function"
