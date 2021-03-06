(**********)
(* erc-vc-extract is a OCaml written program that 
 * extracts verification conditions of an annotated ERC program
 * written by Sewon Park @ KAIST (2019).
 *
 * exporter.ml: the file is a part of erc-vc-extract contains 
 * functions that export the extracted conditions to a Coq source code.
*)
open Context
open Typing
open Ast
open Logic
open Log
open Initialcoq
open Errors
open Loader


(* Coq's type in Coq Libraries Z from ZAriths and R from Reals *)
let dump_type (a : data_type) : string = 
	match a with 
	| Real -> "R"
	| Int -> "Z"
	| _ -> raise (EngineErr "not valid datatype")

(* typed variable list in Coq's function input syntax *)
let rec print_tv_list (tv : typed_variable list) = 
	match tv with
	| (t, v) :: l -> " "^v^" : "^(dump_type t)^(print_tv_list l)
	| [] -> ""

(* Aterm tree into Coq's term. Type tagging in Coq will be done in proposition level *)
let rec dump_atermtree (at : atermtree) : string = 
	match at with 
	|	AZConst z -> (string_of_int z)
	|   ARConst z -> (string_of_int z)
	|   Prec z -> ("(prec "^ (dump_atermtree z))^")"
	|   APlus (t1, t2) -> "("^(dump_atermtree t1)^" + "^(dump_atermtree t2)^")"
	|   AMult (t1, t2) -> "("^(dump_atermtree t1)^" * "^(dump_atermtree t2)^")"
	|   ADiv (t) -> "/ "^(dump_atermtree t)
	|   AMinus (t) -> "- "^(dump_atermtree t)
	|   AVariable s -> s
	|   AApplication (s, l) -> "("^s^" "^(dump_atermtree_list l)^" )"
	|   AProjection (s, i) -> (dump_atermtree s)^"["^(dump_atermtree i)^"]" 
	|   ASub (s, t, e) -> (dump_atermtree s)^"["^(dump_atermtree t)^"=>"^(dump_atermtree e)^"]"
	|   AInput -> raise (EngineErr "predicate cannot be parsed")

and dump_atermtree_list (al : atermtree list) =
	match al with
	| v :: [] -> (dump_atermtree v)
	| v :: l -> (dump_atermtree v)^" "^(dump_atermtree_list l)
	| _ -> ""


let rec dump_foltree (f : foltree) (ctx : (string, data_type) Hashtbl.t)= 
	match f with
	|	True -> "True"
	|   False -> "False"
	|   Identity (t1, t2) -> let t = atermtree_type t1 ctx in
								(match t with
								| Some t ->
								 "("^(dump_atermtree t1)^"="^(dump_atermtree t2)^")%"^(dump_type t)
								| None -> raise (EngineErr ("export]ill typed"^(print_foltree f)^"\nin"^(print_context ctx)))
								)
	|   Neg (f1) -> "~("^(dump_foltree f1 ctx)^")"
	|   Greater (t1, t2) -> let t = atermtree_type t1 ctx in 
							(match t with
							| Some t ->
							"("^(dump_atermtree t1)^">"^(dump_atermtree t2)^")%"^(dump_type t )
							| None -> raise (EngineErr ("export]ill typed"^(print_foltree f)))
							)
	|   Implication (f1, f2) -> "("^(dump_foltree f1 ctx)^" -> "^(dump_foltree f2 ctx)^")"
	|   UniversialQ (s, dt, f) -> let nc = Hashtbl.copy ctx in Hashtbl.add nc s dt; "forall "^s^" : "^(dump_type dt)^", ("^(dump_foltree f nc)^")"
	|   ExistensialQ (s, dt, f) -> let nc = Hashtbl.copy ctx in Hashtbl.add nc s dt; "exists "^s^" : "^(dump_type dt)^", ("^(dump_foltree f nc)^")"
	|   Disjunction (f1, f2) -> "("^(dump_foltree f1 ctx)^" \\/ "^(dump_foltree f2 ctx)^")"
	|   Conjunction (f1, f2) -> "("^(dump_foltree f1 ctx)^" /\\ "^(dump_foltree f2 ctx)^")"
	|   Predicate (s, tl) -> "("^s^" "^(dump_atermtree_list tl)^" )"


let rec dump_datatype_list_dom (ds : data_type list) : string = 
	match ds with
	| d :: [] -> 
		(match d with
		| Real -> "R  "
		| Int -> "Z  "
		| _ -> raise (EngineErr "type of domain can only be either R or Z"))
	| d :: s -> 
		(match d with
		| Real -> "R -> "
		| Int -> "Z -> "
		| _ -> raise (EngineErr "type of domain can only be either R or Z"))
	| _ -> ""



(**********)
(* translate prove obligations to coq *)
let rec dump_sfun_list (fs : (string * (data_type list * data_type)) list) =
	match fs with
	| (s, (dl, cd)) :: l -> "Parameter "^s^" : "^(dump_datatype_list_dom dl)^" -> "^(dump_type cd)^".\n"^(dump_sfun_list l)
	| _ -> ""

let rec new_variables_of_types (dl : data_type list) : typed_variable list =
	match dl with
	| d :: l -> 
		let fv = !freshvar + 1 in 
		freshvar := !freshvar +1;
		(d, "_in"^(string_of_int fv)) :: (new_variables_of_types l)
	| [] -> []


let rec dump_pdefi_fedin (f : foltree) (tv : typed_variable list) (i : int) =
	match tv with
	| (t, v) :: l -> dump_pdefi_fedin (fol_replace f ("@"^(string_of_int i)) (AVariable v)) l (i+1)
	| [] -> f

let rec dump_typed_vars_list (tv : typed_variable list) =
	match tv with
	| (t, v) :: l -> "("^v^" : "^(dump_type t)^")"^(dump_typed_vars_list l)
	| _ -> ""

let rec dump_pdefi_list (f : (string * (data_type list * foltree)) list) =
	match f with 
	| (s, (dl, f)) :: l -> 
		let tv = new_variables_of_types dl in
		let nc = Hashtbl.copy empty_ctx in 
		(match load_input_ctx nc tv with
		| Some ctx ->
			"Definition "^s^" "^(dump_typed_vars_list tv)^" := "^(dump_foltree (dump_pdefi_fedin f tv 1) ctx)^".\n\n"
			^(dump_pdefi_list l)
		| _ -> raise (EngineErr "cannot load"))
	| _ -> ""

let dump_pdefi (): string = 
	let pdefi_list = fold_t pdefi in
	"(**********)\n(* Definition of predicates *)\n\n"^
	(dump_pdefi_list (pdefi_list))^
	"\n\n\n"

let dump_sfun (): string =
	let sfun_list = fold_t sfun in
	"(**********)\n(* Single valued functions loaded to the language *)\n\n"^
	(dump_sfun_list sfun_list)^
	"\n\n\n"


let rec dump_theories_list (l : foltree list ) : string = 
	match l with
	| f :: l -> let b = "Axiom axiom"^(string_of_int (!theoremid))^" : \n\t" in 
				(theoremid := !theoremid+1);
				b^(dump_foltree f empty_ctx)^".\n\n"^(dump_theories_list l)
	| [] -> ""

let dump_theories () : string =
	"(**********)\n(* Assumed axioms *)\n\n"^
	(dump_theories_list !theories)^
	"\n\n\n"

let rec dump_coq_theories_list (l : string list) : string = 
	match l with
	| t :: l -> 
		let b = "Axiom axiomCoq"^(string_of_int (!theoremid))^" : \n\t" in
		(theoremid := !theoremid+1);
		b^t^".\n\n"^(dump_coq_theories_list l)
	| [] ->""

let dump_coq_theories () : string = 
	"(**********)\n(* Assumed Coq axioms *)\n\n"^
	(dump_coq_theories_list (!coq_theories))

let rec dump_theorems (l : foltree list) : string =
	match l with
	| f :: lk -> 
		let b = "Theorem theorem"^(string_of_int (!theoremid))^" : \n\t" in 
		(theoremid := !theoremid+1);
		b^(dump_foltree f empty_ctx)^".\nProof.\nAdmitted.\n\n"^(dump_theorems lk)
	| [] -> ""

let dump_coq_init () : unit = 
	let oc = open_out ((!coqfilename)^"_prec.v") in
	Printf.fprintf oc "%s\n"
	(coqprec);
	close_out oc

let dump_precondition (p : foltree) (tv : typed_variable list) : string = 
	let nc = Hashtbl.copy empty_ctx in
	match load_input_ctx nc tv with
	| Some ctx -> dump_foltree p ctx
	| None -> raise ( EngineErr("dumping precondition"))

let dump_postcondition (p : foltree) (tv : typed_variable list) (rt : data_type) : string = 
	let nc = Hashtbl.copy empty_ctx in
	match load_input_ctx nc tv with
	| Some ctx ->  Hashtbl.add nc "@res" rt; dump_foltree p nc
	| None -> raise ( EngineErr "cannot load inputs")


let dump_init () : string = 
	dump_coq_init ();
	(fmatter)^
	"\nRequire Import Reals.\nRequire Import ZArith.\nRequire Import "^(!filename_wo_dir)^"_prec.\n"


(**********)
(* generate a Coq source code with global contexts (including axioms) 
 * at its header and theorems in f written below
 *)
let dump_coq (f : foltree list) : unit =
	let tv = !parsed_input in
	let s = !parsed_stmt in
	let t = !parsed_return in
	let p = !parsed_precond in
	let q = !parsed_postcond in

	let oc = open_out ((!coqfilename)^".v") in
	Printf.fprintf oc "%s\n"
	((dump_init())^
	("\n\n\n(* Proving correctness of the following program:\n *\n * Precondition: "^(dump_precondition p tv)^"\n *\n * Input: "^(print_tv_list tv)^"\n *\n *"^
	(print_stree_ind_comment s (S O))^"\n *\n * Return "^(print_ttree t)^"\n *\n * Postcondition: "^(dump_postcondition q tv (!parsed_return_type))^
	"*)\n\n\n")^
	(dump_sfun())^
	(dump_pdefi())^
	(dump_theories)()^
	dump_coq_theories()^
	"\n(**********)\n(* put your supplementary lemmas and definitions here *)\n\n\n(**********)\n(* Theorems to be proven *)\n\n"^
	(dump_theorems f));
	close_out oc

let dump_log () : unit =
	let oc = open_out ((!coqfilename)^"_log.txt") in
	Printf.fprintf oc "%s\n"
	(!reduction_log);
	close_out oc
