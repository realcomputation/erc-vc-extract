open Ast
open Context
open Typing
open Errors
open Utilities
open Logic


(* load the programming variables *)
(* let rec load_pvariables (s : statementtree) : unit =
	match s with
	|   Sequence (s1, s2)  -> load_pvariables s1; load_pvariables s2

	|   Newvariable (s, t) -> Hashtbl.add pvariables s true

	| _ -> () *)

let rec load_pvariables_pre (s : statement_pre) : unit =
	match s with
	|   Sequence_pre (_, s1, s2)  -> load_pvariables_pre s1; load_pvariables_pre s2

	|   Newvariable_pre (_, s, t) -> Hashtbl.add pvariables s true

	| _ -> ()



(* Try loading given list of typed variables into the given context *)
let rec load_input_ctx (ctx : (string, data_type) Hashtbl.t) (vl : typed_variable list) = 
	match vl with
	| (tp, s) :: vl -> (if (ctx_mem ctx s) then None else (Hashtbl.add ctx s tp; load_input_ctx ctx vl))
	| _ -> Some ctx


(* Try loading multi/single valued functions *)
let load_mfun (s : string) (d : (data_type list) * data_type) : bool =
	if (ctx_mem empty_ctx s) then false else (Hashtbl.add mfun s d; true)

let load_sfun (s : string) (d : (data_type list) * data_type) : bool =
	if (ctx_mem empty_ctx s) then false else (Hashtbl.add sfun s d; true)

let rec fun_spec_type (s : string) (d : (data_type list) * data_type) (f : (fol_pre * fol_pre) list) : (foltree * foltree) list = 
	match f with
	| f :: l ->
		let ctx = Hashtbl.copy empty_ctx in
		let nvr = typed_list (fst d) 1 in 
		(match load_input_ctx ctx nvr with
		| Some ctx -> 
			let ctxf = Hashtbl.copy ctx in
			Hashtbl.add ctxf "@res" (snd d);
			let pre = foltree_type_pre (fst f) ctx in
			let post = foltree_type_pre (snd f) ctxf in
			(pre, post) :: fun_spec_type s d l

		| None -> raise (CtxLoadErr (ctx, nvr)))
	| [] -> []

let load_mfun_spec (s : string) (d : (data_type list) * data_type) (f : (fol_pre * fol_pre) list) : unit = 
	let fl = fun_spec_type s d f in
	Hashtbl.add mfunfol s fl

(* transform a spec format into a quantified fol statement *)
let spec_to_theory (s : string) (d : (data_type list) * data_type) (f : (foltree * foltree)) : foltree =
	let (dom, codom) = f in
	let tvs = bind_list (fst d) (fun k -> fresh_of_type k) in
	let names = snd (split_list tvs) in 
	let vars = merge_list (snd (split_list (typed_list (fst d) 1))) (bind_list names (fun k -> AVariable k)) in
	let props = Implication(dom, codom) in
	universial_from_list tvs (fol_replace_list props ( ("@res", AApplication (s, bind_list names (fun k -> AVariable k)))::vars ))

(**)
let rec load_theories (th : fol_pre list) : unit =
	match th with
	| t :: tl -> theories := (foltree_type_pre t empty_ctx :: !theories); load_theories tl
	| [] -> ()

let rec load_theories_post (th : foltree list) : unit =
	match th with
	| t :: tl -> theories := (t :: !theories); load_theories_post tl
	| [] -> ()


let load_sfun_spec (s : string) (d : (data_type list) * data_type) (f : (fol_pre * fol_pre) list) = 
	let fl = fun_spec_type s d f in
	load_theories_post (bind_list fl (fun k -> spec_to_theory s d k));
	Hashtbl.add sfunfol s fl

let rec load_pdefi (s : string) (d : data_type list) (f : fol_pre) : unit =
	let ctx = Hashtbl.copy empty_ctx in
	let nvr = typed_list d 1 in
	(match load_input_ctx ctx nvr with
		| Some ctx ->  Hashtbl.add pdefi s (d, foltree_type_pre f ctx)
		| _ -> raise (CtxLoadErr (ctx, nvr)))


let load_program (precond : fol_pre) (postcond : fol_pre) (vr : typed_variable list) (s : statement_pre) (rt : term_pre) =
	(* initialize context *)
		let ctx : (string, data_type) Hashtbl.t = Hashtbl.create 10 in
		(load_pvariables_pre s);
		match load_input_ctx ctx vr with
	  	| Some ctx ->
		(
			let pre_checked = foltree_type_pre precond ctx in
			let ctxo = Hashtbl.copy ctx in
			let (ctxf, stmt) = statementtree_type_pre s ctx false in
			let (tp, tt) = termtree_type_pre rt ctxf in
			Hashtbl.add ctxo "@res" tp;
			let post_checked = foltree_type_pre postcond ctxo in
			begin
				parsed_precond := pre_checked;
				parsed_postcond := post_checked;
				parsed_stmt := stmt;
				parsed_return := tt;
				parsed_input := vr;
				parsed_return_type := tp;
				parsed_final_ctx := Hashtbl.copy ctxf
			end
	 	)
		| _ -> raise (CtxLoadErr (ctx, vr))
	

