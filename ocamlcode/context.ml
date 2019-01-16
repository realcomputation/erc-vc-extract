open Hashtbl
open Ast

(* index used to introduce a fresh variables *)
let freshvar : int ref =  ref 0

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



