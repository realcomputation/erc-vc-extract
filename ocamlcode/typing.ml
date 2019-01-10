open Hashtbl
open Datatype
open Ast
open Context
open Errors

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

(** Type checking for assertion language *)
let rec aterm_type (lt : aterm) (ctx : (string, data_type) Hashtbl.t) = 
	match lt with
	|	AZConst z -> Some Int
	|   ARConst z -> Some Real
	|   Prec t -> (match aterm_type t ctx with
					| Some Int -> Some Real
					| _ -> None)
	|   APlus (t1, t2) -> (match aterm_type t1 ctx, aterm_type t2 ctx with
							| Some Real, Some Real -> Some Real
							| Some Int, Some Int -> Some Int
							| _, _ -> None)
	|   AMult (t1, t2) -> (match aterm_type t1 ctx, aterm_type t2 ctx with
							| Some Real, Some Real -> Some Real
							| _, _ -> None)
	|   ADiv t -> (match aterm_type t ctx with
							| Some Real-> Some Real
							| _ -> None)
	|   AMinus t -> (match aterm_type t ctx with
							| Some Real-> Some Real
							| Some Int-> Some Int
							| _ -> None)
	|   AVariable s -> (if ctx_mem ctx s then Some (Hashtbl.find ctx s) else None)
	
	|   AApplication (s, tl) -> (match aterm_list_type tl ctx with
								| Some tl ->
									(if Hashtbl.mem sfun s then
										(if type_list_check tl (fst (Hashtbl.find sfun s)) then (Some (snd (Hashtbl.find sfun s))) else None)
									else None)

								| _ -> None)
	|   AProjection (a, i) ->	(match aterm_type a ctx, aterm_type i ctx with
								| Some (Inta _), Some Int -> Some Int
								| Some (Reala _), Some Int -> Some Real
								| _,_ -> None
								) 							

	|   ASub (s, t, e) -> 
							(match aterm_type s ctx, aterm_type t ctx, aterm_type e ctx with
							| Some (Inta d), Some Int, Some Int -> Some (Inta d)
							| Some (Reala d), Some Int, Some Real -> Some (Reala d)
							| _, _, _ -> None
							) 
	|   AInput -> None


and aterm_list_type (t : aterm list) (ctx : (string, data_type) Hashtbl.t) = 
	match t with
	| t :: l -> (match aterm_type t ctx, aterm_list_type l ctx with
				| Some tp, Some lv -> Some (tp :: lv)
				| _, _ -> None
				)
	| [] -> Some []

let rec foltree_well_typed (ft : foltree) (ctx : (string, data_type) Hashtbl.t) =
	match ft with
	| True -> true
	| False -> true
	| Identity (t1, t2) -> (match aterm_type t1 ctx, aterm_type t2 ctx with
							| Some Real, Some Real -> true
							| Some Int, Some Int -> true
							| _, _ -> false)
	| Neg (f) -> foltree_well_typed f ctx 
	| Greater (t1, t2) -> (match aterm_type t1 ctx, aterm_type t2 ctx with
							| Some Real, Some Real -> true
							| Some Int, Some Int -> true
							| _, _ -> false)
	| Implication (f1, f2) -> if foltree_well_typed f1 ctx then (if foltree_well_typed f2 ctx then true else false) else false
	| UniversialQ (s, t, f) -> if ctx_mem ctx s || Hashtbl.mem pvariables s || Hashtbl.mem lvariables s then false else (Hashtbl.add lvariables s true; let ctxc = Hashtbl.copy ctx in (Hashtbl.add ctxc s t; foltree_well_typed f ctxc))
	| ExistensialQ (s, t, f) -> if ctx_mem ctx s || Hashtbl.mem pvariables s || Hashtbl.mem lvariables s then false else (Hashtbl.add lvariables s true; let ctxc = Hashtbl.copy ctx in (Hashtbl.add ctxc s t; foltree_well_typed f ctxc))
	| Disjunction (f1, f2) -> (foltree_well_typed f1 ctx) && (foltree_well_typed f2 ctx)
	| Conjunction (f1, f2) -> (foltree_well_typed f1 ctx) && (foltree_well_typed f2 ctx) 
	| Predicate (s, tl) -> (match aterm_list_type tl ctx with
							| Some tl -> 
								(if Hashtbl.mem pdefi s then (if type_list_check (fst (Hashtbl.find pdefi s)) tl then true else false) else false)
							| _ -> false
							)

let rec foltree_well_typed_list (ft : foltree list) (ctx : (string, data_type) Hashtbl.t) =
	match ft with
	| f :: l -> foltree_well_typed f ctx && (foltree_well_typed_list l ctx)
	| [] -> true

(** Type checking for programming language *)
let rec term_type (t : termtree) (ctx : (string, data_type) Hashtbl.t ): data_type option =
	match t with
	|	Variable s -> (if (Hashtbl.mem ctx s) then Some (Hashtbl.find ctx s) else None)
	
	|   Const z -> (Some Int)
	
	|   RConst z -> (Some Real)
	
	|   Mult (t1, t2) -> (match term_type t1 ctx, term_type t2 ctx with
							| Some Real, Some Real -> Some Real
							| _, _ -> None)
	
	|   Plus (t1, t2) -> (match term_type t1 ctx, term_type t2 ctx with
							| Some Int, Some Int -> Some Int
							| Some Real, Some Real -> Some Real
							| _, _ -> None)
	|   Minus t -> (match term_type t ctx with
						| Some Int -> Some Int
						| Some Real -> Some Real
						| _ -> None)

	|   Div t -> (match term_type t  ctx with
							| Some Real -> Some Real
							| _ -> None)

	(*	Boolean related operations *)	
	|   Eq (t1, t2) -> (match term_type t1 ctx, term_type t2 ctx with
							| Some Int, Some Int -> Some Int
							| _, _ -> None)

	|   Gt (t1, t2) -> (match term_type t1 ctx, term_type t2 ctx with
							| Some Real, Some Real -> Some Int
							| _, _ -> None)
	
	|   Neg (t) -> (match term_type t ctx with
							| Some Int -> Some Int
							| _ -> None)
	
	|   And (t1, t2) -> (match term_type t1 ctx, term_type t2 ctx with
							| Some Int, Some Int -> Some Int
							| _, _ -> None)
	
	|   Or (t1, t2) -> (match term_type t1 ctx, term_type t2 ctx with
							| Some Int, Some Int -> Some Int
							| _, _ -> None)

	(*	Primitive functions *)
	|   Select (tl) -> if term_list_type_int tl ctx then Some Int else None
	
	|   Iota (t) -> (match term_type t ctx with
							| Some Int -> Some Real
							| _-> None)
	
	|   Max (t1, t2) -> (match term_type t1 ctx, term_type t2 ctx with
							| Some Int, Some Int -> Some Int
							| Some Real, Some Real -> Some Real
							| _, _ -> None)

	|   Inlinecond (t1, t2, t3) -> (match term_type t1 ctx, term_type t2 ctx, term_type t3 ctx with
									| Some Int, Some Real, Some Real -> Some Real
									| _, _, _ -> None)
	(*	ETC *)
	|   Access (s, t) -> if Hashtbl.mem ctx s then 
							(match Hashtbl.find ctx s, term_type t ctx with 
							|  (Inta n), Some Int -> Some Int
							|  (Reala n), Some Int -> Some Real
							| _, _ -> None) else None

	|   Application (s, tl) -> (match term_list_type tl ctx with
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
	|   Test (z) -> (match term_type z ctx with
					| Some Int -> Some Int
					| _ -> None)

and term_list_type (t : termtree list) (ctx : (string, data_type) Hashtbl.t ): (data_type list) option =
	match t with
	| t :: l -> (match term_type t ctx, term_list_type l ctx with
				| Some tp, Some lv -> Some (tp :: lv)
				| _, _ -> None
				)
	| [] -> Some []

and term_list_type_int (t : termtree list) (ctx : (string, data_type) Hashtbl.t) : bool =
	match t with
	| t :: l -> (match term_type t ctx with
				| Some Int -> term_list_type_int l ctx
				| _ -> false)
	| [] -> true
	

let rec welltypedstatement (s : statementtree) (ctx : (string, data_type) Hashtbl.t) (readonly : bool) =
	match s with
	|   Sequence (s1, s2)  -> (match welltypedstatement s1 ctx false with
								| Some c -> welltypedstatement s2 c false
								| None -> None )

	|   Newvariable (s, t) -> if readonly then None else (if (ctx_mem ctx s) then (None) else (
								match term_type t ctx with
								| Some Real -> (let ctxc = Hashtbl.copy ctx in (Hashtbl.add ctxc s Real; Some ctxc))
								| Some Int -> (let ctxc = Hashtbl.copy ctx in (Hashtbl.add ctxc s Int; Some ctxc))
								| _ -> None))

	|   Assignment (s, t) -> (if (Hashtbl.mem ctx s) then (
								match Hashtbl.find ctx s, term_type t ctx with
								| Real, Some Real -> Some ctx
								| Int, Some Int -> Some ctx
								| _, _ -> None) else (None))

	|   ArrayAssign (s, t, e) -> (if Hashtbl.mem ctx s then (
									match Hashtbl.find ctx s, term_type t ctx, term_type e ctx with
									| Reala _, Some Int, Some Real -> Some ctx
									| Inta _, Some Int, Some Int -> Some ctx
									| _, _, _ -> None) else None)

	|   Conditional (z, s1, s2) -> (match term_type z ctx with
									| Some Int -> (match (welltypedstatement s1 ctx true, welltypedstatement s2 ctx true) with
													| Some _, Some _ -> Some ctx
													| _, _ -> None)
									| _ -> None)

	|   Whileloop (z, s, i, v) -> 
		(if foltree_well_typed i ctx then
			(match aterm_type v ctx with
			| Some _ -> (match term_type z ctx with
							| Some Int -> (match welltypedstatement s ctx true with
											| Some _ -> Some ctx
											| None -> None)
							| _ -> None)
			| _ -> None)
		else None)

	|   Empty -> Some ctx


