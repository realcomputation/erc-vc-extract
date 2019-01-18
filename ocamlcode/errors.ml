open Hashtbl
open Ast
open Context
open Utilities
(* unintended engine error... *)
exception EngineErr of string
exception LoadFail of string

(* user fault errors; it will be called when we type check user provided erc program*)
exception TypeInferErrAterm of ((string, data_type) Hashtbl.t) * aterm_pre
exception TypeInferErrFol of ((string, data_type) Hashtbl.t) * fol_pre
exception TypeInferErr of ((string, data_type) Hashtbl.t) * term_pre
exception TypeInferErrStmt of ((string, data_type) Hashtbl.t) * statement_pre

exception CtxLoadErr of ((string, data_type) Hashtbl.t) * (typed_variable list)


let print_error (e : exn): string  = 
	match e with
	| TypeInferErrAterm (ctx, at) -> 
		let (p, s) = print_aterm_pre at in
		 "cannot infer the type of the logical term in" ^(print_infile p)^":\n\n"^s^"\n\nunder context:\n\n"^(print_context ctx)
	| TypeInferErrFol (ctx, at) ->
		let (p, s) = print_fol_pre at in
		 "cannot infer the type of the fol statement in" ^(print_infile p)^":\n\n"^s^"\n\nunder context:\n\n"^(print_context ctx)
	| TypeInferErr (ctx, at) ->
		let (p, s) = print_term_pre at in
	 	"cannot infer the type of the programming term in" ^(print_infile p)^":\n\n"^s^"\n\nunder context:\n\n"^(print_context ctx)
	| TypeInferErrStmt (ctx, at) ->
		let (p, s) = print_statement_pre at in
 		"cannot infer the type of the type in" ^(print_infile p)^":\n\n"^s^"\n\nunder context:\n\n"^(print_context ctx)
 	| EngineErr s -> "fetal error "^s

	| LoadFail _ -> "cannot load"

	| CtxLoadErr (ctx, vr) ->
		"cannot load input variables:\n"^(unfold_list (bind_list vr (fun (t, s) -> s^" : "^(print_type t))) "" (fun a b -> a^b))^"\n"^
		"into context:\n"^(print_context ctx)



	| _ -> "not recognizable error!"