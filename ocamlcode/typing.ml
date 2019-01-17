open Hashtbl
open Ast
open Context
open Errors
open Utilities

(* Type Checking *)
let rec type_list_check (tl : data_type list) (tr : data_type list) : bool = 
	match tl, tr with
	| t1 :: tl, t2::tr -> (match t1, t2 with
							| Real, Real -> type_list_check tl tr
							| Int, Int -> type_list_check tl tr
							| _, _ -> false
							)
	| [], [] -> true
	| _, _ -> false





(** Type checking for assertion language; raise error if its ill--typed; designed to type check user program *)
let rec atermtree_type_pre (lt : aterm_pre) (ctx : (string, data_type) Hashtbl.t) = 
	match lt with
	|	AZConst_pre (_, z) -> Int
	|   ARConst_pre (_, z) -> Real
	|   Prec_pre (_, t) -> 
		(match atermtree_type_pre t ctx with
		| Int -> Real
		| _ -> raise (TypeInferErrAterm lt))

	|   APlus_pre (_, t1, t2) -> 
		(match atermtree_type_pre t1 ctx, atermtree_type_pre t2 ctx with
		| Real, Real -> Real
		| Int, Int -> Int
		| _, _ -> raise (TypeInferErrAterm lt))
	
	|   AMult_pre (_, t1, t2) -> 
		(match atermtree_type_pre t1 ctx, atermtree_type_pre t2 ctx with
		| Real, Real -> Real
		| _, _ -> raise (TypeInferErrAterm lt))

	|   ADiv_pre (_, t) -> 
		(match atermtree_type_pre t ctx with
		| Real-> Real
		| _ -> raise (TypeInferErrAterm lt))
	
	|   AMinus_pre (_, t) -> 
		(match atermtree_type_pre t ctx with
		| Real-> Real
		| Int-> Int
		| _ -> raise (TypeInferErrAterm lt))

	|   AVariable_pre (_, s) -> 
		(if ctx_mem ctx s then (Hashtbl.find ctx s) else raise (TypeInferErrAterm lt))
	
	|   AApplication_pre (_, s, tl) -> 
		let tlist = bind_list tl (fun l -> atermtree_type_pre l ctx) in
			(if Hashtbl.mem sfun s then
				(if type_list_check tlist (fst (Hashtbl.find sfun s)) then ((snd (Hashtbl.find sfun s))) else raise (TypeInferErrAterm lt))
			else raise (TypeInferErrAterm lt))

	|   AProjection_pre (_, a, i) ->	
		(match atermtree_type_pre a ctx, atermtree_type_pre i ctx with
		| (Inta _), Int -> Int
		| (Reala _), Int -> Real
		| _,_ -> raise (TypeInferErrAterm lt)) 							

	|   ASub_pre (_, s, t, e) -> 
		(match atermtree_type_pre s ctx, atermtree_type_pre t ctx, atermtree_type_pre e ctx with
		| (Inta d), Int, Int -> (Inta d)
		| (Reala d), Int, Real -> (Reala d)
		| _, _, _ -> raise (TypeInferErrAterm lt)
		)

	|   AInput_pre _ -> raise (TypeInferErrAterm lt)





(* type checking without raising error: to be used in the engine *)
(** Type checking for assertion language; return None if its ill--typed *)
let rec atermtree_type (lt : atermtree) (ctx : (string, data_type) Hashtbl.t) = 
	match lt with
	|	AZConst ( z) -> Some Int
	|   ARConst ( z) -> Some Real
	|   Prec ( t) -> 
		(match atermtree_type t ctx with
		| Some Int -> Some Real
		| _ -> None)

	|   APlus ( t1, t2) -> 
		(match atermtree_type t1 ctx, atermtree_type t2 ctx with
		| Some Real, Some Real -> Some Real
		| Some Int, Some Int -> Some Int
		| _, _ -> None)
	
	|   AMult ( t1, t2) -> 
		(match atermtree_type t1 ctx, atermtree_type t2 ctx with
		| Some Real, Some Real -> Some Real
		| _, _ -> None)

	|   ADiv ( t) -> 
		(match atermtree_type t ctx with
		| Some Real-> Some Real
		| _ -> None)
	
	|   AMinus ( t) -> 
		(match atermtree_type t ctx with
		| Some Real-> Some Real
		| Some Int-> Some Int
		| _ -> None)

	|   AVariable ( s) -> 
		(if ctx_mem ctx s then Some (Hashtbl.find ctx s) else None)
	
	|   AApplication (s, tl) -> 
		(match atermtree_list_type tl ctx with
		| Some tl ->
			(if Hashtbl.mem sfun s then
				(if type_list_check tl (fst (Hashtbl.find sfun s)) then (Some (snd (Hashtbl.find sfun s))) else None)
			else None)

		| _ -> None)

	|   AProjection (a, i) ->	
		(match atermtree_type a ctx, atermtree_type i ctx with
		| Some (Inta _), Some Int -> Some Int
		| Some (Reala _), Some Int -> Some Real
		| _,_ -> None) 							

	|   ASub (s, t, e) -> 
		(match atermtree_type s ctx, atermtree_type t ctx, atermtree_type e ctx with
		| Some (Inta d), Some Int, Some Int -> Some (Inta d)
		| Some (Reala d), Some Int, Some Real -> Some (Reala d)
		| _, _, _ -> None
		)

	|   AInput -> None

and atermtree_list_type (t : atermtree list) (ctx : (string, data_type) Hashtbl.t) = 
	match t with
	| t :: l -> (match atermtree_type t ctx, atermtree_list_type l ctx with
				| Some tp, Some lv -> Some (tp :: lv)
				| _, _ -> None
				)
	| [] -> Some []



let rec foltree_type (ft : foltree) (ctx : (string, data_type) Hashtbl.t) =
	match ft with
	| True -> true
	| False -> true
	| Identity (t1, t2) -> (match atermtree_type t1 ctx, atermtree_type t2 ctx with
							| Some Real, Some Real -> true
							| Some Int, Some Int -> true
							| _, _ -> false)
	| Neg (f) -> foltree_type f ctx 
	| Greater (t1, t2) -> (match atermtree_type t1 ctx, atermtree_type t2 ctx with
							| Some Real, Some Real -> true
							| Some Int, Some Int -> true
							| _, _ -> false)
	| Implication (f1, f2) -> if foltree_type f1 ctx then (if foltree_type f2 ctx then true else false) else false
	| UniversialQ (s, t, f) -> if ctx_mem ctx s || Hashtbl.mem pvariables s || Hashtbl.mem lvariables s then false else (Hashtbl.add lvariables s true; let ctxc = Hashtbl.copy ctx in (Hashtbl.add ctxc s t; foltree_type f ctxc))
	| ExistensialQ (s, t, f) -> if ctx_mem ctx s || Hashtbl.mem pvariables s || Hashtbl.mem lvariables s then false else (Hashtbl.add lvariables s true; let ctxc = Hashtbl.copy ctx in (Hashtbl.add ctxc s t; foltree_type f ctxc))
	| Disjunction (f1, f2) -> (foltree_type f1 ctx) && (foltree_type f2 ctx)
	| Conjunction (f1, f2) -> (foltree_type f1 ctx) && (foltree_type f2 ctx) 
	| Predicate (s, tl) -> (match atermtree_list_type tl ctx with
							| Some tl -> 
								(if Hashtbl.mem pdefi s then (if type_list_check (fst (Hashtbl.find pdefi s)) tl then true else false) else false)
							| _ -> false
							)

let rec foltree_type_list (ft : foltree list) (ctx : (string, data_type) Hashtbl.t) =
	match ft with
	| f :: l -> foltree_type f ctx && (foltree_type_list l ctx)
	| [] -> true

(** Type checking for programming language *)
let rec termtree_type (t : termtree) (ctx : (string, data_type) Hashtbl.t ): data_type option =
	match t with
	|	Variable s -> (if (Hashtbl.mem ctx s) then Some (Hashtbl.find ctx s) else None)
	
	|   Const z -> (Some Int)
	
	|   RConst z -> (Some Real)
	
	|   Mult (t1, t2) -> (match termtree_type t1 ctx, termtree_type t2 ctx with
							| Some Real, Some Real -> Some Real
							| _, _ -> None)
	
	|   Plus (t1, t2) -> (match termtree_type t1 ctx, termtree_type t2 ctx with
							| Some Int, Some Int -> Some Int
							| Some Real, Some Real -> Some Real
							| _, _ -> None)
	|   Minus t -> (match termtree_type t ctx with
						| Some Int -> Some Int
						| Some Real -> Some Real
						| _ -> None)

	|   Div t -> (match termtree_type t  ctx with
							| Some Real -> Some Real
							| _ -> None)

	(*	Boolean related operations *)	
	|   Eq (t1, t2) -> (match termtree_type t1 ctx, termtree_type t2 ctx with
							| Some Int, Some Int -> Some Int
							| _, _ -> None)

	|   Gt (t1, t2) -> (match termtree_type t1 ctx, termtree_type t2 ctx with
							| Some Real, Some Real -> Some Int
							| _, _ -> None)
	
	|   Neg (t) -> (match termtree_type t ctx with
							| Some Int -> Some Int
							| _ -> None)
	
	|   And (t1, t2) -> (match termtree_type t1 ctx, termtree_type t2 ctx with
							| Some Int, Some Int -> Some Int
							| _, _ -> None)
	
	|   Or (t1, t2) -> (match termtree_type t1 ctx, termtree_type t2 ctx with
							| Some Int, Some Int -> Some Int
							| _, _ -> None)

	(*	Primitive functions *)
	|   Select (tl) -> if termtree_list_type_int tl ctx then Some Int else None
	
	|   Iota (t) -> (match termtree_type t ctx with
							| Some Int -> Some Real
							| _-> None)
	
	|   Max (t1, t2) -> (match termtree_type t1 ctx, termtree_type t2 ctx with
							| Some Int, Some Int -> Some Int
							| Some Real, Some Real -> Some Real
							| _, _ -> None)

	|   Inlinecond (t1, t2, t3) -> (match termtree_type t1 ctx, termtree_type t2 ctx, termtree_type t3 ctx with
									| Some Int, Some Real, Some Real -> Some Real
									| _, _, _ -> None)
	(*	ETC *)
	|   Access (s, t) -> if Hashtbl.mem ctx s then 
							(match Hashtbl.find ctx s, termtree_type t ctx with 
							|  (Inta n), Some Int -> Some Int
							|  (Reala n), Some Int -> Some Real
							| _, _ -> None) else None

	|   Application (s, tl) -> (match termtree_list_type tl ctx with
								| Some tl ->
									(match Hashtbl.mem sfun s, Hashtbl.mem mfun s with
									| true, false -> 
										let dt = Hashtbl.find sfun s in
										if type_list_check tl (fst dt) then Some (snd dt) else None

									| false, true ->
										let dt = Hashtbl.find mfun s in
										if type_list_check tl (fst dt) then Some (snd dt) else None
									| _, _->  None
									)
								| _ -> None
								)
	|   Test (z) -> (match termtree_type z ctx with
					| Some Int -> Some Int
					| _ -> None)

and termtree_list_type (t : termtree list) (ctx : (string, data_type) Hashtbl.t ): (data_type list) option =
	match t with
	| t :: l -> (match termtree_type t ctx, termtree_list_type l ctx with
				| Some tp, Some lv -> Some (tp :: lv)
				| _, _ -> None
				)
	| [] -> Some []

and termtree_list_type_int (t : termtree list) (ctx : (string, data_type) Hashtbl.t) : bool =
	match t with
	| t :: l -> (match termtree_type t ctx with
				| Some Int -> termtree_list_type_int l ctx
				| _ -> false)
	| [] -> true
	

let rec statementtree_type (s : statementtree) (ctx : (string, data_type) Hashtbl.t) (readonly : bool) =
	match s with
	|   Sequence (s1, s2)  -> (match statementtree_type s1 ctx false with
								| Some c -> statementtree_type s2 c false
								| None -> None )

	|   Newvariable (s, t) -> if readonly then None else (if (ctx_mem ctx s) then (None) else (
								match termtree_type t ctx with
								| Some Real -> (let ctxc = Hashtbl.copy ctx in (Hashtbl.add ctxc s Real; Some ctxc))
								| Some Int -> (let ctxc = Hashtbl.copy ctx in (Hashtbl.add ctxc s Int; Some ctxc))
								| _ -> None))

	|   Assignment (s, t) -> (if (Hashtbl.mem ctx s) then (
								match Hashtbl.find ctx s, termtree_type t ctx with
								| Real, Some Real -> Some ctx
								| Int, Some Int -> Some ctx
								| _, _ -> None) else (None))

	|   ArrayAssign (s, t, e) -> (if Hashtbl.mem ctx s then (
									match Hashtbl.find ctx s, termtree_type t ctx, termtree_type e ctx with
									| Reala _, Some Int, Some Real -> Some ctx
									| Inta _, Some Int, Some Int -> Some ctx
									| _, _, _ -> None) else None)

	|   Conditional (z, s1, s2) -> (match termtree_type z ctx with
									| Some Int -> (match (statementtree_type s1 ctx true, statementtree_type s2 ctx true) with
													| Some _, Some _ -> Some ctx
													| _, _ -> None)
									| _ -> None)

	|   Whileloop (z, s, i, v) -> 
		(if foltree_type i ctx then
			(match atermtree_type v ctx with
			| Some _ -> (match termtree_type z ctx with
							| Some Int -> (match statementtree_type s ctx true with
											| Some _ -> Some ctx
											| None -> None)
							| _ -> None)
			| _ -> None)
		else None)

	|   Empty -> Some ctx


