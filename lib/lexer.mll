{
open Core
open Lexing
open Parser

exception SyntaxError of string

let keywords =
  Hashtbl.of_alist_exn
    (module String)
    [
      ("if", IF);
      ("then", THEN);
      ("else", ELSE);
      ("let", LET);
      ("fun", FUN);
      ("in", IN);
      ("sample", SAMPLE);
      ("observe", OBSERVE);
    ]
}

let blank = [' ' '\t']+
let newline = '\r' | '\n' | "\r\n"
let id = ['a'-'z' 'A'-'Z' '_'] ['a'-'z' 'A'-'Z' '0'-'9' '_' '\'']*

let digit = ['0'-'9']
let int = digit+
let pow = ['e' 'E'] ['+' '-']? int
let real = ((int '.'? | (digit* '.' int))) pow?

rule read =
  parse
  | blank     { read lexbuf }
  | newline   { new_line lexbuf; read lexbuf }
  | int as i  { INT (int_of_string i) }
  | real as r { REAL (float_of_string r) }
  | id as s   { match Hashtbl.find keywords s with Some s -> s | None -> ID s }
  | '#'       { comment lexbuf }
  | '+'       { PLUS }
  | "+."      { RPLUS }
  | '-'       { MINUS }
  | "-."      { RMINUS }
  | "~-"      { NEG }
  | "~-."     { RNEG }
  | '*'       { MULT }
  | "*."      { RMULT }
  | '/'       { DIV }
  | "/."      { RDIV }
  | '='       { EQ }
  | "!="      { NE }
  | '<'       { LT }
  | '>'       { GT }
  | '&'       { AND }
  | '|'       { OR }
  | '!'       { NOT }
  | '('       { LPAREN }
  | ')'       { RPAREN }
  | '['       { LBRACK }
  | ']'       { RBRACK }
  | '{'       { LBRACE }
  | '}'       { RBRACE }
  | ','       { COMMA }
  | ':'       { COLON }
  | ';'       { SEMICOLON }
  | eof       { EOF }
  | _         { raise (SyntaxError ("Unexpected char: " ^ lexeme lexbuf)) }

and comment =
  parse
  | newline { read lexbuf }
  | eof     { EOF }
  | _       { comment lexbuf }
