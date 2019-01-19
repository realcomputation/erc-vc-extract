(**********)
(* erc-vc-extract is a OCaml written program that 
 * extracts verification conditions of an annotated ERC program
 * written by Sewon Park @ KAIST (2019).
 *
 * main.ml: the file is a part of erc-vc-extract contains
 * main function which initiate parsing a given user ERC program
*)
open String 
open Logic
open Vccalc
open Exporter
open Context
open Errors 
open List
open Ast

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
					| exn -> 
				        (
				        let curr = lexbuf.Lexing.lex_curr_p in
				        let line = curr.Lexing.pos_lnum in
				        let token = Lexing.lexeme lexbuf in
				        if token = "" then print_endline (print_error exn)
 						else print_endline ("Cannot parse "^token^" in line "^(string_of_int line));
				    	) 
					)
				else print_endline "file extension .erc expected"
	| _ -> print_endline "file extension .erc expected"

let _ = Printexc.print main ()