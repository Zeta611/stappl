{
 open Parser
 exception Eof
 exception LexicalError
 let verbose1 s =  (print_string s; print_newline()); s
 let verbose2 s =  (print_string s; print_newline()); ()

 (* let verbose1 s =  s
 let verbose2 s =  () *)
 let keyword_tbl = Hashtbl.create 31
 let _ = List.iter (fun (keyword, tok) -> Hashtbl.add keyword_tbl keyword tok)
                   [
                  ("if", IF);
                  ("then", THEN);
                  ("else", ELSE);
                  ("let", LET);
                  ("in", IN);
                  ("sample", SAMPLE);
                  ("observe", OBSERVE);
                   ]
}

let blank = [' ' '\t' '\n' '\r']+
let id = ['a'-'z' 'A'-'Z' '_']['a'-'z' 'A'-'Z' '0'-'9' '_']*
let number = ['0'-'9']+
let newline = ['\n' '\r']+

rule start = parse
      | blank { start lexbuf }
      | number as num { NUM (int_of_string (verbose1 num)) }
      | id as s { let id = verbose1 (String.lowercase_ascii s) in
               try Hashtbl.find keyword_tbl id
               with Not_found -> ID id
            }
      | "#" {verbose2 "#"; comment lexbuf }
      | "+" {verbose2 "+"; PLUS}
      | "-" {verbose2 "-"; MINUS}
      | "*" {verbose2 "*"; MULT}
      | "/" { verbose2 "/"; DIV}
      | "=" { verbose2 "="; EQ}
      | "!=" { verbose2 "!="; NOTEQ}
      | "<" { verbose2 "<"; LESS}
      | ">" { verbose2 ">"; GREAT}
      | "&" { verbose2 "&"; AND}
      | "|" { verbose2 "|"; OR}
      | "!" { verbose2 "!"; NOT}
      | "(" { verbose2 "("; LPAREN}
      | ")" { verbose2 ")"; RPAREN}
      | "[" { verbose2 "["; LSQUARE}
      | "]" { verbose2 "]"; RSQUARE}
      | "," { verbose2 ","; COMMA}
      | "{" { verbose2 "{"; LBRACKET}
      | "}" { verbose2 "}"; RBRACKET}
      | ":" { verbose2 ":"; COLON}
      | ";" { verbose2 ";"; SEMICOLON}
      | eof { verbose2 "eof"; EOF }
      | _ as c { failwith (Printf.sprintf "unexpected character: %C" c) }

and comment = parse
   | newline { start lexbuf }
   | eof { verbose2 "eof"; EOF }
   | _   { comment lexbuf }
