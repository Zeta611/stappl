type id = string
type exp =
  | CONST of int
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
  | NOT of exp
  | LIST of exp list
  | RECORD of (exp * exp) list
  | ASSIGN of id * exp * exp
  | IF of exp * exp * exp
  | CALL of id * exp list
  | SAMPLE of exp
  | OBSERVE of exp * exp
  
type program = EXP of exp | FUNC of id * id list * exp * program

let rec exp_to_str = function
  | CONST i -> string_of_int i
  | VAR x -> x
  | ADD (e1, e2) -> "(" ^ exp_to_str e1 ^ " + " ^ exp_to_str e2 ^ ")"
  | MINUS (e1, e2) -> "(" ^ exp_to_str e1 ^ " - " ^ exp_to_str e2 ^ ")"
  | MULT (e1, e2) -> "(" ^ exp_to_str e1 ^ " * " ^ exp_to_str e2 ^ ")"
  | DIV (e1, e2) -> "(" ^ exp_to_str e1 ^ " / " ^ exp_to_str e2 ^ ")"
  | EQ (e1, e2) -> "(" ^ exp_to_str e1 ^ " = " ^ exp_to_str e2 ^ ")"
  | NOTEQ (e1, e2) -> "(" ^ exp_to_str e1 ^ " != " ^ exp_to_str e2 ^ ")"
  | LESS (e1, e2) -> "(" ^ exp_to_str e1 ^ " < " ^ exp_to_str e2 ^ ")"
  | AND (e1, e2) ->  "(" ^ exp_to_str e1 ^ " & " ^ exp_to_str e2 ^ ")"
  | OR (e1, e2) -> "(" ^ exp_to_str e1 ^ " | " ^ exp_to_str e2 ^ ")"
  | NOT e -> "not " ^ exp_to_str e
  | LIST li -> "[" ^ list_to_str li ^ "]"
  | RECORD li -> 
    let rec record_to_str = function
    | [] -> ""
    | (e1, e2)::tl -> exp_to_str e1 ^ ": " ^ exp_to_str e2 ^ ", " ^ record_to_str tl
    in "{" ^ record_to_str li ^ "}"
  | ASSIGN (x, e1, e2) -> x ^ " = " ^ exp_to_str e1 ^ " in " ^ exp_to_str e2
  | IF (e1, e2, e3) -> "if " ^ exp_to_str e1 ^ " then " ^ exp_to_str e2 ^ " else " ^ exp_to_str e3
  | CALL (x, li) -> x ^ "(" ^ list_to_str li ^ ")"
  | SAMPLE e -> "sample " ^ exp_to_str e
  | OBSERVE (e1, e2) -> "observe (" ^ exp_to_str e1 ^ ", " ^ exp_to_str e2 ^ ")"
and list_to_str = function
  | [] -> ""
  | hd::tl -> exp_to_str hd ^ ", " ^ list_to_str tl

let rec arglist_to_str = function
  | [] -> ""
  | hd::tl -> hd ^ ", " ^ arglist_to_str tl

let rec pgm_to_str = function
  | EXP e -> exp_to_str e
  | FUNC (x, li, e, pgm) -> "let " ^ x ^ "(" ^ arglist_to_str li ^ ") = " ^ exp_to_str e ^ ";\n" ^ pgm_to_str pgm

let pp pgm = print_endline (pgm_to_str pgm)