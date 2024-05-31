open Core

type id = string [@@deriving sexp]

type exp =
  | INT of int
  | REAL of float
  | VAR of id
  | ADD of exp * exp
  | MINUS of exp * exp
  | MULT of exp * exp
  | DIV of exp * exp
  | EQ of exp * exp
  | NOTEQ of exp * exp
  | LESS of exp * exp
  | AND of exp * exp
  | OR of exp * exp
  | SEQ of exp * exp
  | NOT of exp
  | LIST of exp list
  | RECORD of (exp * exp) list
  | ASSIGN of id * exp * exp
  | IF of exp * exp * exp
  | CALL of id * exp list
  | SAMPLE of exp
  | OBSERVE of exp * exp
[@@deriving sexp]

type program = { funs : (id * id list * exp) list; exp : exp } [@@deriving sexp]

let pp pgm = print_endline (sexp_of_program pgm |> Sexp.to_string_hum)
