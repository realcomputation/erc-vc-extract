open Ast
open Context
open Typing
open Errors
open Utilities
open Logic


(* load the programming variables *)
let rec load_pvariables (s : statementtree) : unit =
	match s with
	|   Sequence (s1, s2)  -> load_pvariables s1; load_pvariables s2

	|   Newvariable (s, t) -> Hashtbl.add pvariables s true

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

let rec load_funfol (s : string) (d : (data_type list) * data_type) (f : (foltree * foltree) list) : bool = 
	match f with
	| f :: l ->
		let ctx = Hashtbl.copy empty_ctx in
		(match load_input_ctx ctx (typed_list (fst d) 1) with
		| Some ctx -> 
			let ctxf = Hashtbl.copy ctx in
			Hashtbl.add ctxf "@res" (snd d);
			if (foltree_type (fst f) ctx) && (foltree_type (snd f) ctxf) then
			load_funfol s d l else false
		| None -> raise (PlainError "cannot load input"))
	| [] -> true

let load_mfunfol (s : string) (d : (data_type list) * data_type) (f : (foltree * foltree) list) = 
	if load_funfol s d f then
	(Hashtbl.add mfunfol s f; true)
	else false

let sfunfol_to_theory (s : string) (d : (data_type list) * data_type) (f : (foltree * foltree)) : foltree =
	let (dom, codom) = f in
	let tvs = bind_list (fst d) (fun k -> fresh_of_type k) in
	let names = snd (split_list tvs) in 
	let vars = merge_list (snd (split_list (typed_list (fst d) 1))) (bind_list names (fun k -> AVariable k)) in
	let props = Implication(dom, codom) in
	universial_from_list tvs (fol_replace_list props ( ("@res", AApplication (s, bind_list names (fun k -> AVariable k)))::vars ))


let rec load_theories (th : foltree list) : bool =
	match th with
	| t :: tl -> if (foltree_type t empty_ctx) then ((theories := t :: !theories) ; load_theories tl) else false
	| [] -> true

let load_sfunfol (s : string) (d : (data_type list) * data_type) (f : (foltree * foltree) list) = 
	if load_funfol s d f
	 && 
		load_theories (bind_list f (fun k -> sfunfol_to_theory s d k)) 
		then
		(Hashtbl.add sfunfol s f; true)
	else false

let rec load_pdefi (s : string) (d : data_type list) (f : foltree) =
	let ctx = Hashtbl.copy empty_ctx in
	(match load_input_ctx ctx (typed_list d 1) with
		| Some ctx -> if (foltree_type f ctx) then (Hashtbl.add pdefi s (d, f); true) else false
		| _ -> false
	)
