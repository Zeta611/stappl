open Project
open Program

let src = ref ""
let opt_pp = ref false

let lexbuf_contents lb =
  let open Lexing in
  let pos = lb.lex_curr_pos in
  let len = lb.lex_buffer_len - lb.lex_curr_pos in
  Bytes.to_string (Bytes.sub lb.lex_buffer pos len)

let () =
  Arg.parse
    [ ("-pp", Arg.Unit (fun _ -> opt_pp := true), "print pgm") ]
    (fun x -> src := x)
    ("Usage : " ^ Filename.basename Sys.argv.(0) ^ " [-option] [filename] ");
  if !opt_pp then
    let lexbuf =
      Lexing.from_channel (if !src = "" then stdin else open_in !src)
    in
    try
      let pgm = Parser.program Lexer.start lexbuf in
      let _ = print_endline "=== Printing Input Program ===" in
      pp pgm;
      let _ = print_endline "=== Gathering Functions ===" in
      let open Compiler in
      let env = gather_functions pgm in
      let _ = print_endline "=== Compiling Output Program ===" in
      let graph, _de = compile''' env Pred.Empty pgm.exp in
      let _ = print_endline "=== Printing Output Program ===" in
      Printf.printf "%s" (Graph.pp graph)
    with Parsing.Parse_error ->
      print_endline ("Parsing Error: " ^ lexbuf_contents lexbuf)
  else print_endline "Please provide one of options! (-pp)"
