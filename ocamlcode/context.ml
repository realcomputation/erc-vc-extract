open Hashtbl
open Ast


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
let return_type_f : data_type ref = ref Int

