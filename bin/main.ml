open Core
open Stappl

let print_position (outx : Out_channel.t) (lexbuf : Lexing.lexbuf) : unit =
  let open Lexing in
  let pos = lexbuf.lex_curr_p in
  fprintf outx "%s:%d:%d" pos.pos_fname pos.pos_lnum
    (pos.pos_cnum - pos.pos_bol + 1)

let parse_with_error (lexbuf : Lexing.lexbuf) : Program.program =
  Parser.program Lexer.start lexbuf

let get_program (filename : string) : Program.program =
  let filename, inx =
    if String.(filename = "-") then ("<stdin>", In_channel.stdin)
    else (filename, In_channel.create filename)
  in
  let lexbuf = Lexing.from_channel inx in
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = filename };

  match parse_with_error lexbuf with
  | prog ->
      In_channel.close inx;
      prog
  | exception Parser.Error ->
      fprintf stderr "%a: syntax error\n" print_position lexbuf;
      In_channel.close inx;
      exit (-1)

let command : Command.t =
  Command.basic ~summary:"The STAPPL Compiler"
    ~readme:(fun () ->
      "STAPPL is a compiler for the STAtically typed Probabilistic Programming \
       Language")
    (let%map_open.Command filename =
       anon (maybe_with_default "-" ("filename" %: Filename_unix.arg_type))
     and pp = flag "-pp" no_arg ~doc:" Pretty print the program" in
     fun () ->
       if pp then get_program filename |> Program.pretty |> print_endline
       else
         get_program filename |> Compiler.compile |> fst |> Graph.pretty
         |> print_endline)

let () = Command_unix.run ~version:"0.1.0" ~build_info:"STAPPL" command
