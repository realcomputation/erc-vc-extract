open Hashtbl
open Datatype
open Ast

let theoremid : int ref =  ref 0
let freshvar : int ref =  ref 0
let coqfilename : string ref = ref ""
let filename_wo_dir : string ref = ref ""
(* Global contexts *)
let empty_ctx : (string, data_type) Hashtbl.t = Hashtbl.create 1

let mfun : (string, (data_type list) * data_type) Hashtbl.t = Hashtbl.create 10
let mfunfol : (string, (foltree * foltree) list) Hashtbl.t = Hashtbl.create 10

let sfun : (string, (data_type list) * data_type) Hashtbl.t = Hashtbl.create 10
let sfunfol : (string, (foltree * foltree) list) Hashtbl.t = Hashtbl.create 10


let pvariables : (string, bool) Hashtbl.t = Hashtbl.create 10
let lvariables : (string, bool) Hashtbl.t = Hashtbl.create 10

let pdefi : (string, (data_type list) * foltree) Hashtbl.t = Hashtbl.create 10
let theories : foltree list ref =  ref []
let coq_theories : string list ref = ref []


let ctx_mem (ctx : (string, data_type) Hashtbl.t) (s : string) : bool =
	if Hashtbl.mem ctx s || Hashtbl.mem sfun s || Hashtbl.mem mfun s || Hashtbl.mem pdefi s then true else false

let return_type_f : data_type ref = ref Int

let rec load_pvariables (s : statementtree) : unit =
	match s with
	|   Sequence (s1, s2)  -> load_pvariables s1; load_pvariables s2

	|   Newvariable (s, t) -> Hashtbl.add pvariables s true

	| _ -> ()


(* Load initial contexts *)
let rec load_input_ctx (ctx : (string, data_type) Hashtbl.t) (vl : typed_variable list) = 
	match vl with
	| (tp, s) :: vl -> (if (ctx_mem ctx s) then None else (Hashtbl.add ctx s tp; load_input_ctx ctx vl))
	| _ -> Some ctx


let load_mfun (s : string) (d : (data_type list) * data_type) : bool =
	if (ctx_mem empty_ctx s) then false else (Hashtbl.add mfun s d; true)

let load_sfun (s : string) (d : (data_type list) * data_type) : bool =
	if (ctx_mem empty_ctx s) then false else (Hashtbl.add sfun s d; true)



