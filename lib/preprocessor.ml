open! Core
open Parse_tree

type subst_map = Id.t Id.Map.t

exception Arity_mismatch of string
exception Unbound_variable of string

let gen_args =
  let cnt = ref 0 in
  fun () ->
    let arg = "$arg" ^ string_of_int !cnt in
    incr cnt;
    arg

let rec subst (env : subst_map) : exp -> exp =
  (* 𝜂-expansion required to avoid infinite recursion *)
  let subst' e = subst env e in

  function
  | (Int _ | Real _ | Bool _) as e -> e
  | Var x -> (
      match Map.find env x with
      | None -> raise (Unbound_variable x)
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
  | If (e_pred, e_con, e_alt) -> If (subst' e_pred, subst' e_con, subst' e_alt)
  | Call (f, args) ->
      let args = List.map ~f:subst' args in
      Call (f, args)
  | Sample e -> Sample (subst' e)
  | Observe (d, e) -> Observe (subst' d, subst' e)
  | List _ -> failwith "List not implemented"
  | Record _ -> failwith "Record not implemented"

let rec inline_one (fn : fn) (prog : program) =
  let rec inline_exp scope (exp : exp) =
    let inline_exp' = inline_exp scope in
    match exp with
    | (Int _ | Real _ | Bool _) as e -> e
    | Var x as e -> if Set.mem scope x then e else raise (Unbound_variable x)
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
    | If (e_pred, e_con, e_alt) ->
        If (inline_exp' e_pred, inline_exp' e_con, inline_exp' e_alt)
    | Call (f, args) ->
        (* A-Normalize the arguments. For example, f(sample(e)) should only evaluate sample(e) once. *)
        let args = List.map ~f:inline_exp' args in
        if Id.(f <> fn.name) then Call (f, args)
        else
          let param_args =
            try List.zip_exn fn.params args
            with _ -> raise (Arity_mismatch fn.name)
          in
          let param_args =
            List.map ~f:(fun (p, a) -> (p, gen_args (), a)) param_args
          in
          let env =
            List.fold param_args ~init:Id.Map.empty ~f:(fun env (p, p', _a) ->
                Map.set env ~key:p ~data:p')
          in
          List.fold param_args ~init:(subst env fn.body)
            ~f:(fun body (_p, p', a) -> Assign (p', a, body))
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
      if Id.(name = fn.name) then { funs = { name; params; body } :: funs; exp }
      else
        let { funs; exp } = inline_one fn { funs; exp } in
        { funs = { name; params; body } :: funs; exp }

let rec inline ({ funs; exp } : program) : exp =
  match funs with [] -> exp | f :: funs -> inline (inline_one f { funs; exp })
