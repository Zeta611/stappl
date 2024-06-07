open! Core
open Program
open Typed_tree

let gen_args =
  let cnt = ref 0 in
  fun () ->
    let arg = "$arg" ^ string_of_int !cnt in
    incr cnt;
    arg

let rec subst (env : Id.t Id.Map.t) (e : Exp.t) =
  let subst' = subst env in
  match e with
  | Int _ | Real _ | Bool _ -> e
  | Var x -> (
      match Map.find env x with
      | None -> failwith ("Unbound variable " ^ x)
      | Some v -> Var v)
  | Add (e1, e2) -> Add (subst' e1, subst' e2)
  | Radd (e1, e2) -> Radd (subst' e1, subst' e2)
  | Minus (e1, e2) -> Minus (subst' e1, subst' e2)
  | Rminus (e1, e2) -> Rminus (subst' e1, subst' e2)
  | Neg e -> Neg (subst' e)
  | Rneg e -> Rneg (subst' e)
  | Mult (e1, e2) -> Mult (subst' e1, subst' e2)
  | Rmult (e1, e2) -> Rmult (subst' e1, subst' e2)
  | Div (e1, e2) -> Div (subst' e1, subst' e2)
  | Rdiv (e1, e2) -> Rdiv (subst' e1, subst' e2)
  | Eq (e1, e2) -> Eq (subst' e1, subst' e2)
  | Req (e1, e2) -> Req (subst' e1, subst' e2)
  | Noteq (e1, e2) -> Noteq (subst' e1, subst' e2)
  | Less (e1, e2) -> Less (subst' e1, subst' e2)
  | Rless (e1, e2) -> Rless (subst' e1, subst' e2)
  | And (e1, e2) -> And (subst' e1, subst' e2)
  | Or (e1, e2) -> Or (subst' e1, subst' e2)
  | Seq (e1, e2) -> Seq (subst' e1, subst' e2)
  | Not e -> Not (subst' e)
  | Assign (x, e1, e2) ->
      Assign (x, subst' e1, subst (Map.set env ~key:x ~data:x) e2)
  | If (cond, yes, no) -> If (subst' cond, subst' yes, subst' no)
  | Call (f, args) ->
      let args = List.map ~f:subst' args in
      Call (f, args)
  | Sample e -> Sample (subst' e)
  | Observe (d, e) -> Observe (subst' d, subst' e)
  | List _ -> failwith "List not implemented"
  | Record _ -> failwith "Record not implemented"

let rec inline_one (fn : fn) (prog : program) =
  let rec inline_exp scope (e : Exp.t) =
    let inline_exp' = inline_exp scope in
    match e with
    | Int _ | Real _ | Bool _ -> e
    | Var x -> if Set.mem scope x then e else failwith ("Unbound variable " ^ x)
    | Add (e1, e2) -> Add (inline_exp' e1, inline_exp' e2)
    | Radd (e1, e2) -> Radd (inline_exp' e1, inline_exp' e2)
    | Minus (e1, e2) -> Minus (inline_exp' e1, inline_exp' e2)
    | Rminus (e1, e2) -> Rminus (inline_exp' e1, inline_exp' e2)
    | Neg e -> Neg (inline_exp' e)
    | Rneg e -> Rneg (inline_exp' e)
    | Mult (e1, e2) -> Mult (inline_exp' e1, inline_exp' e2)
    | Rmult (e1, e2) -> Rmult (inline_exp' e1, inline_exp' e2)
    | Div (e1, e2) -> Div (inline_exp' e1, inline_exp' e2)
    | Rdiv (e1, e2) -> Rdiv (inline_exp' e1, inline_exp' e2)
    | Eq (e1, e2) -> Eq (inline_exp' e1, inline_exp' e2)
    | Req (e1, e2) -> Req (inline_exp' e1, inline_exp' e2)
    | Noteq (e1, e2) -> Noteq (inline_exp' e1, inline_exp' e2)
    | Less (e1, e2) -> Less (inline_exp' e1, inline_exp' e2)
    | Rless (e1, e2) -> Rless (inline_exp' e1, inline_exp' e2)
    | And (e1, e2) -> And (inline_exp' e1, inline_exp' e2)
    | Or (e1, e2) -> Or (inline_exp' e1, inline_exp' e2)
    | Seq (e1, e2) -> Seq (inline_exp' e1, inline_exp' e2)
    | Not e -> Not (inline_exp' e)
    | Assign (x, e1, e2) ->
        Assign (x, inline_exp' e1, inline_exp (Set.add scope x) e2)
    | If (cond, yes, no) ->
        If (inline_exp' cond, inline_exp' yes, inline_exp' no)
    | Call (f, args) ->
        let args = List.map ~f:inline_exp' args in
        if Id.(equal f fn.name) then
          let kvpair =
            try List.zip_exn fn.params args
            with _ ->
              failwith
                ("Argument length mismatch when calling function " ^ fn.name)
          in
          let kvpair = List.map ~f:(fun (k, v) -> (k, gen_args (), v)) kvpair in
          let env =
            List.fold kvpair ~init:Id.Map.empty ~f:(fun acc (k, v, _) ->
                Map.set acc ~key:k ~data:v)
          in
          List.fold kvpair ~init:(subst env fn.body) ~f:(fun acc (_, v, arg) ->
              Exp.Assign (v, arg, acc))
        else Call (f, args)
    | Sample e -> Sample (inline_exp' e)
    | Observe (d, e) -> Observe (inline_exp' d, inline_exp' e)
    | List _ -> failwith "List not implemented"
    | Record _ -> failwith "Record not implemented"
  in
  let { funs; exp } = prog in
  match funs with
  | [] -> { funs = []; exp = inline_exp Id.Set.empty exp }
  | { name; params; body } :: funs ->
      let body = inline_exp (Id.Set.of_list params) body in
      if Id.(equal name fn.name) then
        { funs = { name; params; body } :: funs; exp }
      else
        let { funs; exp } = inline_one fn { funs; exp } in
        { funs = { name; params; body } :: funs; exp }

let rec inline (prog : program) =
  let { funs; exp } = prog in
  match funs with
  | [] -> exp
  | fn :: funs -> inline (inline_one fn { funs; exp })

let get_dist (name : Id.t) : any_dist =
  let open Owl.Stats in
  match name with
  | "bernoulli" ->
      Any
        {
          ret = Tyb;
          name = "bernoulli";
          params = [ Tyr ];
          sampler = (fun [ (Tyr, p) ] -> binomial_rvs ~p ~n:1 = 1);
          log_pmdf =
            (fun [ (Tyr, p) ] b -> binomial_logpdf ~p ~n:1 (Bool.to_int b));
        }
  | "normal" ->
      Any
        {
          ret = Tyr;
          name = "normal";
          params = [ Tyr; Tyr ];
          sampler = (fun [ (Tyr, mu); (Tyr, sigma) ] -> gaussian_rvs ~mu ~sigma);
          log_pmdf =
            (fun [ (Tyr, mu); (Tyr, sigma) ] -> gaussian_logpdf ~mu ~sigma);
        }
  | _ -> failwith "Unknown primitive function"

let rec check : type a. tyenv -> Exp.t -> a ty -> (a, non_det) texp =
 fun tyenv e ty ->
  match e with
  | Var x -> (
      match Map.find tyenv x with
      | None -> failwith ("Unbound variable " ^ x)
      | Some (Any t) -> (
          match (t, ty) with
          | Tyi, Tyi -> { ty; exp = Var x }
          | Tyr, Tyr -> { ty; exp = Var x }
          | Tyb, Tyb -> { ty; exp = Var x }
          | _, _ -> failwith ("Variable " ^ x ^ " type mismatch")))
  | Int i -> (
      match ty with
      | Tyi -> { ty; exp = Value i }
      | _ -> failwith "Expected something other than int")
  | Add (e1, e2) -> (
      match ty with
      | Tyi -> check_bop tyenv "+" ( + ) Tyi Tyi Tyi e1 e2
      | _ -> failwith "Expected something other than int")
  | Minus (e1, e2) -> (
      match ty with
      | Tyi -> check_bop tyenv "-" ( - ) Tyi Tyi Tyi e1 e2
      | _ -> failwith "Expected something other than int")
  | Neg e -> (
      match ty with
      | Tyi -> check_uop tyenv "-" Int.neg Tyi Tyi e
      | _ -> failwith "Expected something other than int")
  | Mult (e1, e2) -> (
      match ty with
      | Tyi -> check_bop tyenv "*" ( * ) Tyi Tyi Tyi e1 e2
      | _ -> failwith "Expected something other than int")
  | Div (e1, e2) -> (
      match ty with
      | Tyi -> check_bop tyenv "/" ( / ) Tyi Tyi Tyi e1 e2
      | _ -> failwith "Expected something other than int")
  | Real r -> (
      match ty with
      | Tyr -> { ty; exp = Value r }
      | _ -> failwith "Expected something other than float")
  | Radd (e1, e2) -> (
      match ty with
      | Tyr -> check_bop tyenv "+" ( +. ) Tyr Tyr Tyr e1 e2
      | _ -> failwith "Expected something other than float")
  | Rminus (e1, e2) -> (
      match ty with
      | Tyr -> check_bop tyenv "-" ( -. ) Tyr Tyr Tyr e1 e2
      | _ -> failwith "Expected something other than float")
  | Rneg e -> (
      match ty with
      | Tyr -> check_uop tyenv "-" Float.neg Tyr Tyr e
      | _ -> failwith "Expected something other than float")
  | Rmult (e1, e2) -> (
      match ty with
      | Tyr -> check_bop tyenv "*" ( *. ) Tyr Tyr Tyr e1 e2
      | _ -> failwith "Expected something other than float")
  | Rdiv (e1, e2) -> (
      match ty with
      | Tyr -> check_bop tyenv "/" ( /. ) Tyr Tyr Tyr e1 e2
      | _ -> failwith "Expected something other than float")
  | Bool b -> (
      match ty with
      | Tyb -> { ty; exp = Value b }
      | _ -> failwith "Expected something other than bool")
  | Eq (e1, e2) -> (
      match ty with
      | Tyb -> check_bop tyenv "=" Int.( = ) Tyi Tyi Tyb e1 e2
      | _ -> failwith "Expected something other than bool")
  | Req (e1, e2) -> (
      match ty with
      | Tyb -> check_bop tyenv "=" Float.( = ) Tyr Tyr Tyb e1 e2
      | _ -> failwith "Expected something other than bool")
  | Noteq (e1, e2) -> (
      match ty with
      | Tyb -> check_bop tyenv "<>" Int.( <> ) Tyi Tyi Tyb e1 e2
      | _ -> failwith "Expected something other than bool")
  | Less (e1, e2) -> (
      match ty with
      | Tyb -> check_bop tyenv "<" Int.( < ) Tyi Tyi Tyb e1 e2
      | _ -> failwith "Expected something other than bool")
  | Rless (e1, e2) -> (
      match ty with
      | Tyb -> check_bop tyenv "<" Float.( < ) Tyr Tyr Tyb e1 e2
      | _ -> failwith "Expected something other than bool")
  | And (e1, e2) -> (
      match ty with
      | Tyb -> check_bop tyenv "&&" ( && ) Tyb Tyb Tyb e1 e2
      | _ -> failwith "Expected something other than bool")
  | Or (e1, e2) -> (
      match ty with
      | Tyb -> check_bop tyenv "||" ( || ) Tyb Tyb Tyb e1 e2
      | _ -> failwith "Expected something other than bool")
  | Not e -> (
      match ty with
      | Tyb -> check_uop tyenv "!" not Tyb Tyb e
      | _ -> failwith "Expected something other than bool")
  | Observe (d, e) -> (
      let (Any td) = convert tyenv d in
      let (Any te) = convert tyenv e in
      match (ty, td.ty, te.ty) with
      | Tyi, Tyi, Tyi -> { ty; exp = Observe (td, te) }
      | Tyr, Tyr, Tyr -> { ty; exp = Observe (td, te) }
      | Tyb, Tyb, Tyb -> { ty; exp = Observe (td, te) }
      | _, _, _ -> failwith "Argument to observe has different types")
  | Seq (e1, e2) ->
      let (Any te1) = convert tyenv e1 in
      let te2 = check tyenv e2 ty in
      { ty; exp = Let ("_", te1, te2) }
  | Assign (x, e1, e2) ->
      let (Any ({ ty = ty1; exp = _ } as te1)) = convert tyenv e1 in
      let tyenv = Map.set tyenv ~key:x ~data:(Any ty1) in
      let te2 = check tyenv e2 ty in
      { ty; exp = Let (x, te1, te2) }
  | If (pred, conseq, alt) ->
      let tpred = check tyenv pred Tyb in
      let tconseq = check tyenv conseq ty in
      let talt = check tyenv alt ty in
      { ty; exp = If (tpred, tconseq, talt) }
  | Call (prim, args) -> (
      let (Any dist) = get_dist prim in
      let args = check_args tyenv args dist.params in
      match (dist.ret, ty) with
      | Tyi, Tyi -> { ty; exp = Call (dist, args) }
      | Tyr, Tyr -> { ty; exp = Call (dist, args) }
      | Tyb, Tyb -> { ty; exp = Call (dist, args) }
      | _, _ -> failwith "No")
  | Sample e ->
      let te = check tyenv e ty in
      { ty; exp = Sample te }
  | List _ -> failwith "List not implemented"
  | Record _ -> failwith "Record not implemented"

and check_uop :
    type arg ret.
    tyenv ->
    Id.t ->
    (arg -> ret) ->
    arg ty ->
    ret ty ->
    Exp.t ->
    (ret, non_det) texp =
 fun tyenv name f t ty e ->
  let te = check tyenv e t in
  { ty; exp = Uop ({ name; f }, te) }

and check_bop :
    type arg1 arg2 ret.
    tyenv ->
    Id.t ->
    (arg1 -> arg2 -> ret) ->
    arg1 ty ->
    arg2 ty ->
    ret ty ->
    Exp.t ->
    Exp.t ->
    (ret, non_det) texp =
 fun tyenv name f t1 t2 ty e1 e2 ->
  let te1 = check tyenv e1 t1 in
  let te2 = check tyenv e2 t2 in
  { ty; exp = Bop ({ name; f }, te1, te2) }

and check_args : type a. tyenv -> Exp.t list -> a params -> (a, non_det) args =
 fun tyenv el tyl ->
  match tyl with
  | [] -> []
  | argty :: argtys -> (
      match el with
      | [] -> failwith "Primitive call failed"
      | arg :: args ->
          let arg = check tyenv arg argty in
          let args = check_args tyenv args argtys in
          arg :: args)

and convert (tyenv : tyenv) (e : Exp.t) : any_ndet =
  match e with
  | Var x -> (
      match Map.find tyenv x with
      | None -> failwith ("Unbound variable " ^ x)
      | Some (Any t) -> Any { ty = t; exp = Var x })
  | Int _ | Add _ | Minus _ | Neg _ | Mult _ | Div _ -> Any (check tyenv e Tyi)
  | Real _ | Radd _ | Rminus _ | Rneg _ | Rmult _ | Rdiv _ ->
      Any (check tyenv e Tyr)
  | Bool _ | Eq _ | Req _ | Noteq _ | Less _ | Rless _ | And _ | Or _ | Not _ ->
      Any (check tyenv e Tyb)
  | Observe (d, e) -> (
      let (Any td) = convert tyenv d in
      let (Any te) = convert tyenv e in
      match (td.ty, te.ty) with
      | Tyi, Tyi -> Any { ty = Tyi; exp = Observe (td, te) }
      | Tyr, Tyr -> Any { ty = Tyr; exp = Observe (td, te) }
      | Tyb, Tyb -> Any { ty = Tyb; exp = Observe (td, te) }
      | _, _ -> failwith "Argument to observe has different types.")
  | Seq (e1, e2) ->
      let (Any te1) = convert tyenv e1 in
      let (Any ({ ty = ty2; exp = _ } as te2)) = convert tyenv e2 in
      Any { ty = ty2; exp = Let ("_", te1, te2) }
  | Assign (x, e1, e2) ->
      let (Any ({ ty = ty1; exp = _ } as te1)) = convert tyenv e1 in
      let tyenv = Map.set tyenv ~key:x ~data:(Any ty1) in
      let (Any ({ ty = ty2; exp = _ } as te2)) = convert tyenv e2 in
      Any { ty = ty2; exp = Let (x, te1, te2) }
  | If (pred, conseq, alt) -> (
      let tpred = check tyenv pred Tyb in
      let (Any tconseq) = convert tyenv conseq in
      let (Any talt) = convert tyenv alt in
      match (tconseq.ty, talt.ty) with
      | Tyi, Tyi -> Any { ty = Tyi; exp = If (tpred, tconseq, talt) }
      | Tyr, Tyr -> Any { ty = Tyr; exp = If (tpred, tconseq, talt) }
      | Tyb, Tyb -> Any { ty = Tyb; exp = If (tpred, tconseq, talt) }
      | _, _ -> failwith "Branches of an if statement must return the same type"
      )
  | Call (prim, args) ->
      let (Any dist) = get_dist prim in
      let args = check_args tyenv args dist.params in
      Any { ty = dist.ret; exp = Call (dist, args) }
  | Sample e ->
      let (Any te) = convert tyenv e in
      Any { ty = te.ty; exp = Sample te }
  | List _ -> failwith "List not implemented"
  | Record _ -> failwith "Record not implemented"
