open Hashtbl
open Ast
open Context
open Errors
open Utilities
open Logic 

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
let rec atermtree_type_pre (lt : aterm_pre) (ctx : (string, data_type) Hashtbl.t) : data_type * atermtree = 
	match lt with
	|	AZConst_pre (_, z) -> (Int, AZConst z)
	|   ARConst_pre (_, z) -> (Real, ARConst z)
	|   Prec_pre (_, t) -> 
		let (dt, at) = atermtree_type_pre t ctx in
		(match dt with
		| Int -> (Real, Prec at)
		| _ -> raise (TypeInferErrAterm (ctx, lt)))

	|   APlus_pre (_, t1, t2) ->
		let (dt1, at1) = atermtree_type_pre t1 ctx in
		let (dt2, at2) = atermtree_type_pre t2 ctx in 
		(match dt1, dt2 with
		| Real, Real -> (Real, APlus (at1, at2))
		| Int, Int -> (Int, APlus (at1, at2))
		| _, _ -> raise (TypeInferErrAterm (ctx, lt)))
	
	|   AMult_pre (_, t1, t2) -> 
		let (dt1, at1) = atermtree_type_pre t1 ctx in
		let (dt2, at2) = atermtree_type_pre t2 ctx in 
		(match dt1, dt2 with
		| Real, Real -> (Real, AMult (at1, at2))
		| _, _ -> raise (TypeInferErrAterm (ctx, lt)))

	|   ADiv_pre (_, t) -> 
		let (dt, at) = atermtree_type_pre t ctx in
		(match dt with
		| Real -> (Real, ADiv at)
		| _ -> raise (TypeInferErrAterm (ctx, lt)))
	
	|   AMinus_pre (_, t) -> 
		let (dt, at) = atermtree_type_pre t ctx in
		(match dt with
		| Int -> (Int, AMinus at)
		| Real -> (Real, AMinus at)
		| _ -> raise (TypeInferErrAterm (ctx, lt)))

	|   AVariable_pre (_, s) -> 
		(if ctx_mem ctx s then (Hashtbl.find ctx s, AVariable s) else raise (TypeInferErrAterm (ctx, lt)))
	
	|   AApplication_pre (_, s, tl) -> 
		let (tlist, tlist_aterm)  = split_list (bind_list tl (fun l -> atermtree_type_pre l ctx)) in	
		(if Hashtbl.mem sfun s then
			(if type_list_check tlist (fst (Hashtbl.find sfun s)) then (snd (Hashtbl.find sfun s), AApplication (s, tlist_aterm)) else raise (TypeInferErrAterm (ctx, lt)))
		else raise (TypeInferErrAterm (ctx, lt)))

	|   AProjection_pre (_, a, i) ->
		let (dt1, at1) = atermtree_type_pre a ctx in
		let (dt2, at2) = atermtree_type_pre i ctx in 
		(match dt1, dt2 with
		| (Inta _), Int -> (Int, AProjection (at1, at2))
		| (Reala _), Int -> (Real, AProjection (at1, at2))
		| _, _ -> raise (TypeInferErrAterm (ctx, lt))) 							

	|   ASub_pre (_, s, t, e) -> 
		let (dt1, at1) = atermtree_type_pre s ctx in
		let (dt2, at2) = atermtree_type_pre t ctx in 
		let (dt3, at3) = atermtree_type_pre e ctx in
		(match dt1, dt2, dt3 with
		| (Inta d), Int, Int -> (Inta d, ASub (at1, at2, at3))
		| (Reala d), Int, Real -> (Reala d, ASub (at1, at2, at3))
		| _, _, _ -> raise (TypeInferErrAterm (ctx, lt)))

	|   AInput_pre _ -> raise (TypeInferErrAterm (ctx, lt))

let rec foltree_type_pre (ft : fol_pre) (ctx : (string, data_type) Hashtbl.t) : foltree =
	match ft with
	| True_pre _  -> True
	| False_pre _ -> False
	| Identity_pre (_, t1, t2) -> 
		(match atermtree_type_pre t1 ctx, atermtree_type_pre t2 ctx with
		| (Real, at1), (Real, at2) -> Identity (at1, at2)
		| (Int,  at1), (Int,  at2) -> Identity (at1, at2)
		| _, _ -> raise (TypeInferErrFol (ctx, ft)))
	| Neg_pre (_, f) -> Neg (foltree_type_pre f ctx)
	| Greater_pre (_, t1, t2) -> 
		(match atermtree_type_pre t1 ctx, atermtree_type_pre t2 ctx with
		| (Real, at1), (Real, at2) -> Greater(at1, at2)
		| (Int, at1), (Int, at2)   -> Greater(at1, at2)
		| _, _ -> raise (TypeInferErrFol (ctx, ft)))
	| Implication_pre (_, f1, f2) -> Implication(foltree_type_pre f1 ctx, foltree_type_pre f2 ctx)
	| UniversialQ_pre (_, s, t, f) -> 
		if ctx_mem ctx s || Hashtbl.mem pvariables s || Hashtbl.mem lvariables s 
		then raise (TypeInferErrFol (ctx, ft)) 
		else (Hashtbl.add lvariables s true; let ctxc = Hashtbl.copy ctx in (Hashtbl.add ctxc s t; UniversialQ(s, t, foltree_type_pre f ctxc)))
	| ExistensialQ_pre (_, s, t, f) -> 
		if ctx_mem ctx s || Hashtbl.mem pvariables s || Hashtbl.mem lvariables s 
		then raise (TypeInferErrFol (ctx, ft))  
		else (Hashtbl.add lvariables s true; let ctxc = Hashtbl.copy ctx in (Hashtbl.add ctxc s t; ExistensialQ(s, t, foltree_type_pre f ctxc)))
	| Disjunction_pre (_, f1, f2) -> Disjunction(foltree_type_pre f1 ctx, foltree_type_pre f2 ctx)
	| Conjunction_pre (_, f1, f2) -> Conjunction(foltree_type_pre f1 ctx, foltree_type_pre f2 ctx)
	| Predicate_pre (_, s, tl) ->
		let (tlist, tlist_aterm)  = split_list (bind_list tl (fun l -> atermtree_type_pre l ctx)) in	
		(if Hashtbl.mem pdefi s then 
			(if type_list_check (fst (Hashtbl.find pdefi s)) tlist then Predicate(s, tlist_aterm) else raise (TypeInferErrFol (ctx, ft))) 
		else raise (TypeInferErrFol (ctx, ft)))


	|   UniqQ_pre (_, s, t, f) -> 
		let w = ("_uniq"^s^(string_of_int (!freshvar +1))) in
		(freshvar := !freshvar+1);
		if ctx_mem ctx s || Hashtbl.mem pvariables s || Hashtbl.mem lvariables s 
		then raise (TypeInferErrFol (ctx, ft))  
		else 
		begin
			Hashtbl.add lvariables s true; 
			let ctxc = Hashtbl.copy ctx in Hashtbl.add ctxc s t; 
			let fbdy = foltree_type_pre f ctxc in
			ExistensialQ (s, t, Conjunction(fbdy, UniversialQ(w, t, Implication(fol_replace fbdy s (AVariable w), Identity (AVariable s, AVariable w)))))
		end

	

	|   LT_pre (_, t1, t2) ->
		let (tp1, at1) = atermtree_type_pre t1 ctx in
		let (tp2, at2) = atermtree_type_pre t2 ctx in
		(match tp1, tp2 with
		| Int, Int -> Greater(at2, at1)
		| Real, Real -> Greater (at2, at1)
		| _, _ -> raise (TypeInferErrFol (ctx, ft))
		) 
	|   GE_pre (_, t1, t2) ->
		let (tp1, at1) = atermtree_type_pre t1 ctx in
		let (tp2, at2) = atermtree_type_pre t2 ctx in
		(match tp1, tp2 with
		| Int, Int -> Disjunction(Identity(at1, at2), Greater(at1, at2))
		| Real, Real -> Disjunction(Identity(at1, at2), Greater(at1, at2))
		| _, _ -> raise (TypeInferErrFol (ctx, ft))
		) 
	|   LE_pre (_, t1, t2) -> 
		let (tp1, at1) = atermtree_type_pre t1 ctx in
		let (tp2, at2) = atermtree_type_pre t2 ctx in
		(match tp1, tp2 with
		| Int, Int -> Disjunction(Identity(at1, at2), Greater(at2, at1))
		| Real, Real -> Disjunction(Identity(at1, at2), Greater(at2, at1))
		| _, _ -> raise (TypeInferErrFol (ctx, ft))
		) 
	
	|   GTGT_pre (_, t1, t2, t3) ->
		let (tp1, at1) = atermtree_type_pre t1 ctx in
		let (tp2, at2) = atermtree_type_pre t2 ctx in
		let (tp3, at3) = atermtree_type_pre t3 ctx in
		(match tp1, tp2, tp3 with
		| Int, Int, Int -> Conjunction(Greater(at1, at2), Greater(at2, at3))
		| Real, Real, Real -> Conjunction(Greater(at1, at2), Greater(at2, at3))
		| _, _, _ -> raise (TypeInferErrFol (ctx, ft)))
	|   GTGE_pre (_, t1, t2, t3) ->
		let (tp1, at1) = atermtree_type_pre t1 ctx in
		let (tp2, at2) = atermtree_type_pre t2 ctx in
		let (tp3, at3) = atermtree_type_pre t3 ctx in
		(match tp1, tp2, tp3 with
		| Int, Int, Int -> Conjunction(Greater(at1, at2), Disjunction(Identity(at2, at3), Greater(at2, at3)))
		| Real, Real, Real -> Conjunction(Greater(at1, at2), Disjunction(Identity(at2, at3), Greater(at2, at3)))
		| _, _, _ -> raise (TypeInferErrFol (ctx, ft)))
	|   GEGT_pre (_, t1, t2, t3) ->
		let (tp1, at1) = atermtree_type_pre t1 ctx in
		let (tp2, at2) = atermtree_type_pre t2 ctx in
		let (tp3, at3) = atermtree_type_pre t3 ctx in
		(match tp1, tp2, tp3 with
		| Int, Int, Int -> Conjunction(Disjunction(Identity(at1, at2), Greater(at1, at2)), Greater(at2, at3))
		| Real, Real, Real -> Conjunction(Disjunction(Identity(at1, at2), Greater(at1, at2)), Greater(at2, at3))
		| _, _, _ -> raise (TypeInferErrFol (ctx, ft)))
	|   GEGE_pre (_, t1, t2, t3) ->
		let (tp1, at1) = atermtree_type_pre t1 ctx in
		let (tp2, at2) = atermtree_type_pre t2 ctx in
		let (tp3, at3) = atermtree_type_pre t3 ctx in
		(match tp1, tp2, tp3 with
		| Int, Int, Int -> Conjunction(Disjunction(Identity(at1, at2), Greater(at1, at2)), Disjunction(Identity(at2, at3), Greater(at2, at3)))
		| Real, Real, Real -> Conjunction(Disjunction(Identity(at1, at2), Greater(at1, at2)), Disjunction(Identity(at2, at3), Greater(at2, at3)))
		| _, _, _ -> raise (TypeInferErrFol (ctx, ft)))
	|   LTLT_pre (_, t1, t2, t3) ->
		let (tp1, at1) = atermtree_type_pre t1 ctx in
		let (tp2, at2) = atermtree_type_pre t2 ctx in
		let (tp3, at3) = atermtree_type_pre t3 ctx in
		(match tp1, tp2, tp3 with
		| Int, Int, Int -> Conjunction(Greater(at3, at2), Greater(at2, at1))
		| Real, Real, Real -> Conjunction(Greater(at3, at2), Greater(at2, at1))
		| _, _, _ -> raise (TypeInferErrFol (ctx, ft)))
	|   LTLE_pre (_, t1, t2, t3) ->
		let (tp1, at1) = atermtree_type_pre t1 ctx in
		let (tp2, at2) = atermtree_type_pre t2 ctx in
		let (tp3, at3) = atermtree_type_pre t3 ctx in
		(match tp1, tp2, tp3 with
		| Int, Int, Int -> Conjunction(Disjunction(Identity(at3, at2), Greater(at3, at2)), Greater(at2, at1))
		| Real, Real, Real -> Conjunction(Disjunction(Identity(at3, at2), Greater(at3, at2)), Greater(at2, at1))
		| _, _, _ -> raise (TypeInferErrFol (ctx, ft)))
	|   LELT_pre (_, t1, t2, t3) ->
		let (tp1, at1) = atermtree_type_pre t1 ctx in
		let (tp2, at2) = atermtree_type_pre t2 ctx in
		let (tp3, at3) = atermtree_type_pre t3 ctx in
		(match tp1, tp2, tp3 with
		| Int, Int, Int -> Conjunction(Greater(at3, at2), Disjunction(Identity(at2, at1), Greater(at2, at1)))
		| Real, Real, Real -> Conjunction(Greater(at3, at2), Disjunction(Identity(at2, at1), Greater(at2, at1)))
		| _, _, _ -> raise (TypeInferErrFol (ctx, ft)))
	|   LELE_pre (_, t1, t2, t3) ->
		let (tp1, at1) = atermtree_type_pre t1 ctx in
		let (tp2, at2) = atermtree_type_pre t2 ctx in
		let (tp3, at3) = atermtree_type_pre t3 ctx in
		(match tp1, tp2, tp3 with
		| Int, Int, Int -> Conjunction(Disjunction(Identity(at3, at2), Greater(at3, at2)), Disjunction(Identity(at2, at1), Greater(at2, at1)))
		| Real, Real, Real -> Conjunction(Disjunction(Identity(at3, at2), Greater(at3, at2)), Disjunction(Identity(at2, at1), Greater(at2, at1)))
		| _, _, _ -> raise (TypeInferErrFol (ctx, ft)))


(** Type checking for programming language *)
let rec termtree_type_pre (pt : term_pre) (ctx : (string, data_type) Hashtbl.t ) : data_type * termtree =
	match pt with
	|	Variable_pre (_, s) -> (if (Hashtbl.mem ctx s) then (Hashtbl.find ctx s, Variable s) else raise (TypeInferErr (ctx, pt)))
	
	|   Const_pre (_, z)  -> (Int, Const z)
	
	|   RConst_pre (_, z)  -> (Real, RConst z)
	
	|   Mult_pre (_, t1, t2) -> 
		(match termtree_type_pre t1 ctx, termtree_type_pre t2 ctx with
		| (Real, at1), (Real, at2) -> (Real, Mult (at1, at2))
		| _, _ -> raise (TypeInferErr (ctx, pt)))

	|   Plus_pre (_, t1, t2) -> 
		(match termtree_type_pre t1 ctx, termtree_type_pre t2 ctx with
		| (Int, at1), (Int, at2) -> (Int, Plus (at1, at2))
		| (Real, at1), (Real, at2) -> (Real, Plus (at1, at2))
		| _, _ -> raise (TypeInferErr (ctx, pt)))
	
	|   Minus_pre (_,t)  -> 
		(match termtree_type_pre t ctx with
		| (Int, at) -> (Int, Minus at)
		| (Real, at) -> (Real, Minus at)
		| _ -> raise (TypeInferErr (ctx, pt)))

	|   Div_pre (_,t)  -> 
		(match termtree_type_pre t  ctx with
		| (Real, at) -> (Real, Div at)
		| _ -> raise (TypeInferErr (ctx, pt)))

	(*	Boolean related operations *)	
	|   Eq_pre (_, t1, t2) -> 
		(match termtree_type_pre t1 ctx, termtree_type_pre t2 ctx with
		| (Int, at1), (Int, at2) -> (Int, Eq (at1, at2))
		| _, _ -> raise (TypeInferErr (ctx, pt)))

	|   Gt_pre (_, t1, t2) -> 
		(match termtree_type_pre t1 ctx, termtree_type_pre t2 ctx with
		| (Real, at1), (Real, at2) -> (Int, Gt (at1, at2))
		| _, _ -> raise (TypeInferErr (ctx, pt)))
	
	|   Neg_pre (_, t) -> 
		(match termtree_type_pre t ctx with
		| (Int, at) -> (Int, Neg at)
		| _ -> raise (TypeInferErr (ctx, pt)))
	
	|   And_pre (_, t1, t2) -> 
		(match termtree_type_pre t1 ctx, termtree_type_pre t2 ctx with
		| (Int, at1), (Int, at2) -> (Int, And (at1, at2))
		| _, _ -> raise (TypeInferErr (ctx, pt)))
	
	|   Or_pre (_, t1, t2) -> 
		(match termtree_type_pre t1 ctx, termtree_type_pre t2 ctx with
		| (Int, at1), (Int, at2) -> (Int, Or (at1, at2))
		| _, _ -> raise (TypeInferErr (ctx, pt)))

	(*	Primitive functions *)
	|   Select_pre (_, tl) -> 
		let (tps, ats) = split_list (bind_list tl (fun l -> termtree_type_pre l ctx)) in
		let bts = bind_list tps (fun tp -> match tp with Int -> true | _ -> false) in
		if unfold_list bts true (fun a b -> a && b) then (Int, Select ats) else raise (TypeInferErr (ctx, pt))
	
	|   Iota_pre (_, t) -> 
		(match termtree_type_pre t ctx with
		| (Int, at) -> (Real, Iota at)
		| _-> raise (TypeInferErr (ctx, pt)))
	
	|   Max_pre (_, t1, t2) -> 
		(match termtree_type_pre t1 ctx, termtree_type_pre t2 ctx with
		| (Int, at1), (Int, at2) -> (Int, Max (at1, at2))
		| (Real, at1), (Real, at2) -> (Real, Max (at1, at2))
		| _, _ -> raise (TypeInferErr (ctx, pt)))

	|   Inlinecond_pre (_, t1, t2, t3) -> 
		(match termtree_type_pre t1 ctx, termtree_type_pre t2 ctx, termtree_type_pre t3 ctx with
		| (Int, at1), (Real, at2), (Real, at3) -> (Real, Inlinecond (at1, at2, at3))
		| _, _, _ -> raise (TypeInferErr (ctx, pt)))
	
	(*	ETC *)
	|   Access_pre (_, s, t) -> 
		if Hashtbl.mem ctx s then 
		(match Hashtbl.find ctx s, termtree_type_pre t ctx with 
		|  (Inta n), (Int, at) -> (Int, Access (s, at))
		|  (Reala n), (Int, at) -> (Real, Access (s, at))
		| _, _ -> raise (TypeInferErr (ctx, pt))) else raise (TypeInferErr (ctx, pt))

	|   Application_pre (_, s, tl) -> 
		let (tps, ats) = split_list (bind_list tl (fun l -> termtree_type_pre l ctx)) in
		(match Hashtbl.mem sfun s, Hashtbl.mem mfun s with
		| true, false -> 
			let dt = Hashtbl.find sfun s in
			if type_list_check tps (fst dt) then (snd dt, Application (s, ats)) else raise (TypeInferErr (ctx, pt))

		| false, true ->
			let dt = Hashtbl.find mfun s in
			if type_list_check tps (fst dt) then (snd dt, Application (s, ats)) else raise (TypeInferErr (ctx, pt))
		| _, _->  raise (TypeInferErr (ctx, pt)))

	|   Test_pre (_, z) -> 
		(match termtree_type_pre z ctx with
		| (Int, at) -> (Int, Test at)
		| _ -> raise (TypeInferErr (ctx, pt)))



let rec statementtree_type_pre (stmt : statement_pre) (ctx : (string, data_type) Hashtbl.t) (readonly : bool) : (string, data_type) Hashtbl.t * statementtree =
	match stmt with
	|   Sequence_pre (_, s1, s2)  -> 
		let (ctx1, so) = statementtree_type_pre s1 ctx readonly in
		let (ctx2, sp) = statementtree_type_pre s2 ctx1 readonly in
		(ctx2, Sequence(so, sp))

	|   Newvariable_pre (_, s, t) -> 
		if readonly then raise (TypeInferErrStmt (ctx, stmt)) else (if (ctx_mem ctx s || Hashtbl.mem lvariables s) then raise (TypeInferErrStmt (ctx, stmt)) else 
			(match termtree_type_pre t ctx with
			| (Real, at) -> (let ctxc = Hashtbl.copy ctx in (Hashtbl.add ctxc s Real; (ctxc, Newvariable (s, at))))
			| (Int, at)  -> (let ctxc = Hashtbl.copy ctx in (Hashtbl.add ctxc s Int;  (ctxc, Newvariable (s, at))))
			| _ -> raise (TypeInferErrStmt (ctx, stmt))))

	|   Assignment_pre (_, s, t) -> 
		(if (Hashtbl.mem ctx s) then 
			(match Hashtbl.find ctx s, termtree_type_pre t ctx with
			| Real, (Real, at) -> (ctx, Assignment (s, at))
			| Int,  (Int,  at) -> (ctx, Assignment (s, at))
			| _, _ -> raise (TypeInferErrStmt (ctx, stmt))) else raise (TypeInferErrStmt (ctx, stmt)))

	|   ArrayAssign_pre (_, s, t, e) -> 
		(if Hashtbl.mem ctx s then (
		match Hashtbl.find ctx s, termtree_type_pre t ctx, termtree_type_pre e ctx with
		| Reala _, (Int, at1), (Real, at2) -> (ctx, ArrayAssign (s, at1, at2))
		| Inta _, (Int, at1), (Int, at2)   -> (ctx, ArrayAssign (s, at1, at2))
		| _, _, _ -> raise (TypeInferErrStmt (ctx, stmt))) else raise (TypeInferErrStmt (ctx, stmt)))

	|   Conditional_pre (_, z, s1, s2) -> 
		(match termtree_type_pre z ctx with
		| (Int, at) -> 
			(match (statementtree_type_pre s1 ctx true, statementtree_type_pre s2 ctx true) with
			| (_, s11), (_, s12) -> (ctx, Conditional(at, s11, s12)))
		| _ -> raise (TypeInferErrStmt (ctx, stmt)))

	|   Whileloop_pre (_, z, s, i, v) -> 
		let fi = foltree_type_pre i ctx in
		let (t, at) = atermtree_type_pre v ctx in
		let (ctxf, bdy) = statementtree_type_pre s ctx true  in
		let (tp, grd) = termtree_type_pre z ctx in
		(match tp with
		| Int -> (ctx, Whileloop(grd, bdy, fi, at))
		| _ -> raise (TypeInferErrStmt (ctx, stmt)))

	|   Empty_pre _ -> (ctx, Empty)


















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
	|   Sequence (s1, s2)  -> (match statementtree_type s1 ctx readonly with
								| Some c -> statementtree_type s2 c readonly
								| None -> None )

	|   Newvariable (s, t) -> if readonly then None else (if (ctx_mem ctx s || Hashtbl.mem lvariables s) then (None) else (
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


