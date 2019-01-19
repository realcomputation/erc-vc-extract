(**********)
(* erc-vc-extract is a OCaml written program that 
 * extracts verification conditions of an annotated ERC program
 * written by Sewon Park @ KAIST (2019).
 *
 * context.ml: the file is a part of erc-vc-extract contains
 * global contexts and variables to be used by the program
 * sfun/mfun is a context storing user defined function symbols
 * freshvar is a global variable that is used when other functions will to
 * introduce a fresh variables.
*)
open Hashtbl
open Ast
open Utilities


(* index used to introduce a fresh variables *)
let freshvar : int ref =  ref 0
let fresh_of_type a =
	let v6 = ("_v"^(string_of_int (!freshvar +1))) in
	(freshvar := !freshvar+1);
	(a, v6)

let rec typed_list (d : data_type list) (i : int) : typed_variable list =
	match d with
	| d :: l -> (d, "@"^(string_of_int i)) :: (typed_list l (i+1))
	| _  -> []

(* index used to introduce a fresh theorem id for Coq export *)
let theoremid : int ref =  ref 0

(* input file name *)
let coqfilename : string ref = ref ""
let filename_wo_dir : string ref = ref ""

(* Global contexts *)
let empty_ctx : (string, data_type) Hashtbl.t = Hashtbl.create 1

(* multi/single value function context *)
let mfun : (string, (data_type list) * data_type) Hashtbl.t = Hashtbl.create 10
let mfunfol : (string, (foltree * foltree) list) Hashtbl.t = Hashtbl.create 10

let sfun : (string, (data_type list) * data_type) Hashtbl.t = Hashtbl.create 10
let sfunfol : (string, (foltree * foltree) list) Hashtbl.t = Hashtbl.create 10

(* introduced programming variables and logical variables *)
let pvariables : (string, bool) Hashtbl.t = Hashtbl.create 10
let lvariables : (string, bool) Hashtbl.t = Hashtbl.create 10




(* predefined predicates *)
let pdefi : (string, (data_type list) * foltree) Hashtbl.t = Hashtbl.create 10

(* assumptions / assumptions in Coq syntax *)
let theories : foltree list ref =  ref []
let coq_theories : string list ref = ref []

(* Check a given context searching also the global contexts *)
let ctx_mem (ctx : (string, data_type) Hashtbl.t) (s : string) : bool =
	if Hashtbl.mem ctx s || Hashtbl.mem sfun s || Hashtbl.mem mfun s || Hashtbl.mem pdefi s then true else false


(* return type stored here...? *)
let parsed_precond : foltree ref = ref True
let parsed_postcond : foltree ref = ref True
let parsed_stmt : statementtree ref = ref Empty
let parsed_return : termtree ref = ref (Const 0)
let parsed_input : typed_variable list ref = ref []
let parsed_return_type : data_type ref = ref Int
let parsed_final_ctx : (string, data_type) Hashtbl.t ref = ref (Hashtbl.create 1) 


let fold_t h =  Hashtbl.fold (fun k v acc -> (k, v) :: acc) h []

let rec print_v_t ( v : (string* data_type) list) =
	match v with
	| (s, t) :: l -> s^" : "^(print_type t)^"\n"^(print_v_t l)
	| [] -> ""

let rec print_f_s (v : (string* ((data_type list) * data_type)) list) : string =
	match v with
	| (s, (d, c)) :: l -> s^" : "^(unfold_list (bind_list d (fun l -> (print_type l)^"*")) "" (fun a b -> a^b))^ " -> "^(print_type c)^"\n"^(print_f_s l)
	| [] -> ""


let print_context ( ctx : (string, data_type) Hashtbl.t) : string =
	(print_v_t (fold_t ctx))^"\n\n"^(print_f_s (fold_t sfun))^"\n\n"^(print_f_s (fold_t mfun))


