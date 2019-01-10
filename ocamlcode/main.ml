open String 
open Logic
open Wpcalc
open Exporter
open Context
open Errors 
open List

let rec lstr (s : string list) =
	match s with
	| s :: l -> s^","^(lstr l)
	| [] -> ""

let main () =
	let fnames = Str.split (Str.regexp "\\.") (Sys.argv.(1)) in 
	match fnames with
	| a :: [b] -> if b = "erc"
					then
					(
					coqfilename := a;
					(match List.rev (Str.split (Str.regexp "/") a) with
					| g :: l -> filename_wo_dir := g
					| [] -> print_endline "cannot parse file name...");
					let file = open_in (Sys.argv.(1)) in
					let lexbuf = Lexing.from_channel(file) in
					try Parser.prog Lexer.token lexbuf
					with
					| TypingError (a, b, c) ->
						print_endline (a^":\n"^b^" is ill-typed under context:\n\n"^(print_context c))
					| PlainError (a) ->
						print_endline a
					| Illtyped s -> print_endline s
					| UnQuant s -> print_endline s
					| LoadFail s -> 
						begin
					        let curr = lexbuf.Lexing.lex_curr_p in
					        let line = curr.Lexing.pos_lnum in
					        print_endline ("Cannot assumption "^s^" in line "^(string_of_int line));
						end

					| exn -> 
				        (
				        let curr = lexbuf.Lexing.lex_curr_p in
				        let line = curr.Lexing.pos_lnum in
				        let token = Lexing.lexeme lexbuf in
				        print_endline ("Cannot parse "^token^" in line "^(string_of_int line));
				    	) 
					)
				else print_endline "file extension .erc expected"
	| _ -> print_endline "file extension .erc expected"

(* 	let file = open_in (fname) in
	let lexbuf = Lexing.from_channel(file) in
		try Parser.prog Lexer.token lexbuf
		with
		| exn -> 
	        (
	        let curr = lexbuf.Lexing.lex_curr_p in
	        let line = curr.Lexing.pos_lnum in
	        let token = Lexing.lexeme lexbuf in
	        print_endline ("Cannot parse "^token^" in line "^(string_of_int line));
	    	)  *)


let _ = Printexc.print main ()