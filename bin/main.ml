open! Core
open Stappl

let print_position (outx : Out_channel.t) (lexbuf : Lexing.lexbuf) : unit =
  let open Lexing in
  let pos = lexbuf.lex_curr_p in
  fprintf outx "%s:%d:%d" pos.pos_fname pos.pos_lnum
    (pos.pos_cnum - pos.pos_bol + 1)

let parse_with_error (lexbuf : Lexing.lexbuf) : Parse_tree.program =
  Parser.program Lexer.read lexbuf

let get_program (filename : string) : Parse_tree.program =
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
     and pp_opt = flag "-pp" no_arg ~doc:" Pretty print the program"
     and graph_opt = flag "-graph" no_arg ~doc:" Print the compiled graph"
     and debug_opt = flag "-debug" no_arg ~doc:" Debug mode" in
     fun () ->
       if debug_opt then Logs.set_level (Some Logs.Debug);

       if pp_opt then (
         printf "Pretty-print: %s\n" filename;
         print_s [%sexp (get_program filename : Parse_tree.program)]);

       let graph_query = ref None in
       if graph_opt then (
         if pp_opt then printf "\n";
         printf "Compile: %s\n" filename;
         Out_channel.flush stdout;
         let graph, query = get_program filename |> Compiler.compile_program in
         graph_query := Some (graph, query);
         print_s [%sexp (Printing.of_graph graph : Printing.graph)]);

       if pp_opt || graph_opt then printf "\n";
       printf "Inference: %s\n" filename;
       Out_channel.flush stdout;
       let graph, query =
         !graph_query
         |> Option.value
              ~default:(get_program filename |> Compiler.compile_program)
       in
       printf "Query result saved at %s\n"
         (Evaluator.infer ~filename graph query))

let () =
  Logs.set_reporter (Logs_fmt.reporter ());
  Command_unix.run ~version:"0.1.0" ~build_info:"STAPPL" command;
  exit (if Logs.err_count () > 0 then 1 else 0)
