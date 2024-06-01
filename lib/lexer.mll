{
open Parser

exception Eof
exception LexicalError

let keyword_tbl = Hashtbl.create 31

let _ =
  List.iter
    (fun (keyword, tok) -> Hashtbl.add keyword_tbl keyword tok)
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

let blank = [' ' '\t' '\n' '\r']+
let id = ['a'-'z' 'A'-'Z' '_']['a'-'z' 'A'-'Z' '0'-'9' '_']*

let digit = ['0'-'9']
let int = digit+
let pow = ['e' 'E']['+' '-']?int
let real = ((int '.'? | (digit* '.' int)))pow?
let newline = ['\n' '\r']+

rule start = parse
      | blank { start lexbuf }
      | int as i { INT (int_of_string i) }
      | real as r { REAL (float_of_string r) }
      | id as s { let id = String.lowercase_ascii s in
               try Hashtbl.find keyword_tbl id
               with Not_found -> ID id
            }
      | "#" { comment lexbuf }
      | "+" { PLUS}
      | "+." { RPLUS}
      | "-" { MINUS}
      | "-." { RMINUS}
      | "~-" { NEG}
      | "~-." { RNEG}
      | "*" { MULT}
      | "*." { RMULT}
      | "/" {  DIV}
      | "/." {  RDIV}
      | "=" {  EQ}
      | "!=" {  NOTEQ}
      | "<" {  LESS}
      | ">" {  GREAT}
      | "&" {  AND}
      | "|" {  OR}
      | "!" {  NOT}
      | "(" {  LPAREN}
      | ")" {  RPAREN}
      | "[" {  LSQUARE}
      | "]" {  RSQUARE}
      | "," {  COMMA}
      | "{" {  LBRACKET}
      | "}" {  RBRACKET}
      | ":" {  COLON}
      | ";" {  SEMICOLON}
      | eof {  EOF }
      | _ as c { failwith (Printf.sprintf "unexpected character: %C" c) }

and comment = parse
   | newline { start lexbuf }
   | eof {  EOF }
   | _   { comment lexbuf }
