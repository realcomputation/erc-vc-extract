(**********)
(* erc-vc-extract is a OCaml written program that 
 * extracts verification conditions of an annotated ERC program
 * written by Sewon Park @ KAIST (2019).
 *
 * reduction.ml: the file is a part of erc-vc-extract contains
 * first order logic simplification methods;
 * fol_reduce : foltree -> foltree is the final function
*)
open Ast
open Canonical
open Logic
open Log
open Errors 

let rec atermtree_simpl (at : atermtree) : atermtree = 
	match at with
	|   Prec t -> Prec (atermtree_simpl t)
	|   APlus (t1, t2) -> 
		(match atermtree_simpl t1, atermtree_simpl t2 with
		| AZConst b1, AZConst b2 -> AZConst (b1 + b2)
		| ARConst b1, ARConst b2 -> ARConst (b1 + b2)
		| AZConst 0, q -> q
		| ARConst 0, q -> q
		| p, AZConst 0 -> p
		| p, ARConst 0 -> p
		| p, q -> APlus(p,q)
		)
	|   AMult (t1, t2) ->
		(match atermtree_simpl t1, atermtree_simpl t2 with
		| ARConst 0, q -> ARConst 0
		| p, ARConst 0 -> ARConst 0
		| ARConst 1, q -> q
		| p, ARConst 1 -> p
		| p, q -> AMult (p, q)
		)
	|   ADiv t -> 
		(match atermtree_simpl t with
		| ARConst 1 -> ARConst 1
		| ARConst (-1) -> ARConst (-1)
		| _ ->	ADiv (atermtree_simpl t)
		)
	|   AMinus t -> 
		(
		match t with
		| AZConst z -> AZConst (- z)
		| ARConst z -> ARConst (- z)
		| _ -> at
		)
	|   _ -> at


let rec fol_atermtree_simpl (ft : foltree) : foltree =
	match ft with
	| Neg (f) -> Neg (fol_atermtree_simpl f)
	| Identity (t1, t2) -> Identity (atermtree_simpl t1, atermtree_simpl t2)
	| Greater (t1, t2) -> Greater (atermtree_simpl t1, atermtree_simpl t2)
	| Implication (f1, f2) -> Implication (fol_atermtree_simpl f1, fol_atermtree_simpl f2)
	| UniversialQ (s, t, f) -> UniversialQ (s, t, fol_atermtree_simpl f)
	| ExistensialQ (s, t, f) -> ExistensialQ (s, t, fol_atermtree_simpl f)
	| Disjunction (f1, f2) -> Disjunction (fol_atermtree_simpl f1, fol_atermtree_simpl f2)
	| Conjunction (f1, f2) -> Conjunction (fol_atermtree_simpl f1, fol_atermtree_simpl f2)
	| _ -> ft


(* simplify truth values *)
let rec simplify_t (l : foltree) = 
(	match l with
	|   Neg (l) ->
		(match simplify_t l with
		| True -> False
		| False -> True
		| p -> Neg p
		)
	|   Implication (l1,l2) -> 
		(match simplify_t l1, simplify_t l2 with
		| _, True -> True
		| True, q -> q
		| False, _ -> True
		| p, q -> Implication(p, q)
		)
	|   UniversialQ (s, dt, ls) ->
		(match simplify_t ls with
		| True -> True
		| False -> False
		| p -> UniversialQ (s, dt, p)
		)
	|   ExistensialQ (s, dt, ls) ->
		(match simplify_t ls with
		| True -> True
		| False -> False
		| p -> ExistensialQ (s, dt, p)
		)
	|   Disjunction (l1, l2) ->
		(match simplify_t l1, simplify_t l2 with
		| True, _ -> True
		| _, True -> True
		| False, False -> False
		| False, q -> q
		| p, False -> p
		| p, q -> Disjunction (p, q)
		)
	|   Conjunction (l1, l2) ->
		(match simplify_t l1, simplify_t l2 with
		| True, True -> True
		| True, q -> q
		| p, True -> p
		| False, _ -> False
		| _, False -> False
		| p, q -> Conjunction (p,q)
		)
	| _ -> l)


let atermtree_neq (a1 : atermtree) (a2 : atermtree) =
	match a1, a2 with
	| AZConst z1, AZConst z2 -> (if z1 = z2 then false else true)
	| ARConst z1, ARConst z2 -> (if z1 = z2 then false else true)
	| _, _ -> false

(**********)
(* simplify a = a -reduce-> True and 1=2 -reduce-> False *)
let rec simplify_i (l : foltree) : foltree =
	match l with
	|   Neg (t) -> Neg (simplify_i t)
	|   Identity (a1, a2) -> 
			let l1 = atermtree_linear_canonical (APlus(a1, AMinus(a2))) in
			let l2 = int_linear_canonical (APlus(a1, AMinus (a2))) in 
			(match l1, l2 with
			| Some lt, _ -> let c = clean_atermtree_linear lt in
						(match c with
						| ([], (0, _)) -> True
						| ([], (_, _)) -> False
						| _ -> l 
						)
			| _, Some lt -> let c = clean_int_linear lt in
						(match c with
						| ([], 0) -> True
						| ([], _) -> False
						| _ -> l
						)
			| _, _ -> if atermtree_eq a1 a2 then True else l
			)
	|   Implication (l1, l2) -> Implication(simplify_i l1, simplify_i l2)
	|   Disjunction (l1, l2) -> Disjunction(simplify_i l1, simplify_i l2)
	|   Conjunction (l1, l2) -> Conjunction(simplify_i l1, simplify_i l2)
	|   UniversialQ (s, dt, fl) -> UniversialQ (s, dt, simplify_i fl)
	|   ExistensialQ (s, dt, fl) -> ExistensialQ (s, dt, simplify_i fl)
	|   _ -> l


(**********)
(* reduce quantifiers *)
let rec find_ex (l : foltree) (s : string) : atermtree list = 
	match l with
	| Conjunction (l1, l2) -> (find_ex l1 s) @ (find_ex l2 s)
	| Identity (AVariable v, AVariable w) -> if v = s then [AVariable w] else (if w = s then [AVariable v] else [])
	| Identity (AVariable v, a) -> if v = s then [a] else []
	| Identity (a, AVariable v) -> if v = s then [a] else []
	| Identity (a, b) -> 
		(match atermtree_linear_canonical (APlus (a, (AMinus b))), int_linear_canonical (APlus (a, (AMinus b))) with
		| Some lin, _ -> 
			(match find_var_linear_identity lin s with
			| Some at -> [ atermtree_simpl at]
			| _ -> []
			)
		| _, Some lint ->
			(match find_var_int_identity lint s with
			| Some at -> [atermtree_simpl at]
			| _ -> []
			)
		| _, _ -> []
		)
	| _ -> []


let rec find_nex (l : foltree) (s : string) : atermtree list =
	match l with 
	| Disjunction (l1, l2) -> find_nex l1 s @ find_nex l2 s
	| Neg(Identity (AVariable a1, a2)) -> if a1 = s then [a2] else []
	| Neg(Identity (a1, AVariable a2)) -> if a2 = s then [a1] else []
	| _ -> []

let rec setup_ex (l : foltree) (s : string) : foltree  =
	match l with
	| Disjunction(l1, l2) -> Disjunction (setup_ex l1 s, setup_ex l2 s)
	| Conjunction(l1, l2) -> 
		(match bounded_var_fol l1 s, bounded_var_fol l2 s with
		| true, true -> 
			(match l1, l2 with
			| Disjunction(r1, r2), _ -> Disjunction(setup_ex (Conjunction(r1,l2)) s,setup_ex (Conjunction(r2, l2)) s)
			| _, Disjunction(r1, r2) -> Disjunction(setup_ex (Conjunction(l1, r1)) s, setup_ex(Conjunction(l1, r2)) s)
			| _, _ -> 
				(match find_ex l s with
				|  a :: _ -> fol_replace l s a
				|   []  -> l
				)
			)
	| true, false -> Conjunction(setup_ex l1 s, l2)
		| false, true -> Conjunction(l1, setup_ex l2 s)
		| false, false -> l
		)							
	| Identity _ -> 
							(match find_ex l s with
							|  [a] -> fol_replace l s a
							|   _  -> l
							)
	| ExistensialQ(s2, d2, el) -> ExistensialQ(s2, d2, setup_ex el s)
	| _ -> l

let rec setup_uni (l : foltree) (s : string) : foltree = 
	(match l with
		| Conjunction(a, b) -> Conjunction(setup_uni a s, setup_uni b s)
		| UniversialQ(s2, d2, l2) -> UniversialQ(s2, d2, setup_uni l2 s)
		| Implication(a, b) -> 
			(match find_ex a s with
			| [t] -> (fol_replace l s t)
			| _ -> 	
				(match find_nex b s with
				| [t] -> fol_replace l s t
				| _ -> 
					(match a, b with
					| Disjunction(p, q), _ -> Conjunction(setup_uni (Implication(p, b)) s, setup_uni (Implication(q, b)) s)
					| _, Conjunction(p, q) -> Conjunction(setup_uni (Implication(a, p)) s, setup_uni (Implication(a, q)) s)
					| _, _ -> 	l
					)
				)
			)
		| _ -> l
	)

let rec split_conjunctions (l : foltree) : foltree list =
	match l with
	| Conjunction (l1, l2) -> split_conjunctions l1 @ split_conjunctions l2
	| UniversialQ (s, d, Conjunction(l1, l2)) -> split_conjunctions (UniversialQ(s, d, l1)) @ split_conjunctions (UniversialQ (s, d, l2))
	| _ -> [l]

let rec print_list (s : string list) =
	match s with
	| s :: l -> (print_endline s); print_list l
	| [] -> ()


let rec reduce_quantifiers (l : foltree) : foltree =
	match l with
	| Neg(f) -> Neg (reduce_quantifiers f)
	| ExistensialQ(s, d, f) -> 	
		let simpl = reduce_quantifiers f in
		let simpli = simplify_i (setup_ex simpl s) in
		if bounded_var_fol simpli s then ExistensialQ(s, d, simpli) else simpli

	| UniversialQ(s, d, f) -> 
		let simpl = reduce_quantifiers f in
		let simpli = simplify_i (setup_uni simpl s) in
		(match simpli with
		| Conjunction(a, b) -> (match bounded_var_fol a s, bounded_var_fol b s with
								| false, false -> simpli
								| true, false -> Conjunction(UniversialQ(s, d, a), b)
								| false, true -> Conjunction(a, UniversialQ(s, d, b))
								| true, true -> UniversialQ(s, d, simpli))
		| _ ->	if bounded_var_fol simpli s then UniversialQ(s, d, simpli) else simpli

		)
		
	| Implication (l1, l2) -> Implication(reduce_quantifiers l1, reduce_quantifiers l2)
	| Disjunction (l1, l2) -> Disjunction(reduce_quantifiers l1, reduce_quantifiers l2)
	| Conjunction (l1, l2) -> Conjunction(reduce_quantifiers l1, reduce_quantifiers l2)
	| _ -> l


let rec reduce_quantifiers_list (l : foltree list) : foltree list =
	match l with
	| f :: l -> reduce_quantifiers f :: reduce_quantifiers_list l
	| [] -> []



(**********)
(* Prenex form of a first order formulae with Q1 Q2 Q3 ... Qn F where
 * F is a quantifier free formulae whose variables are bounded by one of Qi.
 * Prenex transform of a first order formula Q is a Prenex form which is 
 * equivalent to the original formula. 
 *
 * Transforming a first order formula into a Prenex form, we transform the
 * quantifier free part into DNF form and reduce as much clauses as possible 
 * by checking conflicts;e.g.,
 * Q /\ Neg Q /\ ... => False
 * We further simplifies using simple arithmetic facts; e.g.,
 * x = 10 /\ x > 10 ... => False
 *
 * DNF transformation may increases the number of clauses. 
 * Hence, our full reduction strategy only "TRY" reduction using
 * Prenex - DNF; if it only increases the number of clauses, 
 * it rolls back!
*)
type quanti = 
		Univ of data_type
	|   Exi of data_type

type tagged_variable = quanti * string

type prenex_form = { quantifiers : tagged_variable list; mainfol : foltree }


(* make l into prenex form *)
let rec prenex (l : foltree) : foltree = 
	match l with
	| Conjunction (a, b) -> 
		let a = prenex a in
		let b = prenex b in
		(match a, b with
		| ExistensialQ(s, d, le), _ -> ExistensialQ(s, d, prenex (Conjunction(le, b)))
		| _, ExistensialQ(s, d, le) -> ExistensialQ(s, d, prenex (Conjunction(a, le)))
		| UniversialQ(s, d, le), _ -> UniversialQ(s, d, prenex (Conjunction(le, b)))
		| _, UniversialQ(s, d, le) -> UniversialQ(s, d, prenex (Conjunction(a, le)))
		| _, _ -> Conjunction(a, b)
		)
	| Disjunction (a, b) ->
		let a = prenex a in
		let b = prenex b in
		(match a, b with
		| ExistensialQ(s, d, le), _ -> ExistensialQ(s, d, prenex (Disjunction(le, b)))
		| _, ExistensialQ(s, d, le) -> ExistensialQ(s, d, prenex (Disjunction(a, le)))
		| UniversialQ(s, d, le), _ -> UniversialQ(s, d, prenex (Disjunction(le, b)))
		| _, UniversialQ(s, d, le) -> UniversialQ(s, d, prenex (Disjunction(a, le)))
		| _, _ -> Disjunction(a, b)
		) 
	| Implication (a, b) ->
		let a = prenex a in
		let b = prenex b in
		(match a, b with
		| ExistensialQ(s, d, le), _ -> UniversialQ(s, d, prenex (Implication(le, b)))
		| _, ExistensialQ(s, d, le) -> ExistensialQ(s, d, prenex (Implication(a, le)))
		| UniversialQ(s, d, le), _ -> ExistensialQ(s, d, prenex (Implication(le, b)))
		| _, UniversialQ(s, d, le) -> UniversialQ(s, d, prenex (Implication(a, le)))
		| _, _ -> Implication(a, b)

		)

	| Neg (f) ->
		let f = prenex f in
		(match f with
		| ExistensialQ(s, d, le) -> UniversialQ(s, d, prenex (Neg (le)))
		| UniversialQ(s, d, le) -> ExistensialQ(s, d, prenex (Neg (le)))
		| _ -> Neg(f)
		)

	| ExistensialQ(s, d, t) -> ExistensialQ(s, d, prenex t)
	| UniversialQ(s, d, t) -> UniversialQ(s, d, prenex t)

	| _ -> l


(* extract the list (preserving orders as well) of quantifiers of a prenex formed f *)
let rec extract_quantifiers (f : foltree) : tagged_variable list =
	match f with
	| ExistensialQ(s, d, t) -> (Exi d, s) :: extract_quantifiers t
	| UniversialQ(s, d, t) -> (Univ d, s) :: extract_quantifiers t
	| _ -> []

(* extract the quantifier free part of a prenex formed f *)
let rec extract_body (f : foltree) : foltree =
	match f with
	| ExistensialQ(s, d, t) -> extract_body t
	| UniversialQ(s, d, t) -> extract_body t
	| _ -> f

(* construct prenex type *)
let prenex_extract (f : foltree) : prenex_form = 
	let f = prenex f in
	{quantifiers = extract_quantifiers f; mainfol = extract_body f}




(**********)
(* building dnf form on a quantifier free f *)
(* reducing implications *)
let rec impl_reduction (f : foltree) : foltree= 
	match f with
	| Neg (f) -> Neg(impl_reduction f)
	| Implication (a, b) -> Disjunction(Neg (impl_reduction a), impl_reduction b)

	| UniversialQ _ -> raise (EngineErr "")
	| ExistensialQ _ -> raise (EngineErr "")

	| Disjunction (a, b) -> Disjunction(impl_reduction a, impl_reduction b)
	| Conjunction (a, b) -> Conjunction(impl_reduction a, impl_reduction b)
	| _ -> f

(* reducing negations so that negation only applies to literals *)
let rec neg_reduction (f : foltree) = 
	match f with
	| Neg (l) ->
	(
		match l with
		| Neg(k) -> neg_reduction k (* double negation elim *)
		| Conjunction(a, b) -> Disjunction(neg_reduction (Neg a), neg_reduction (Neg b))
		| Disjunction(a, b) -> Conjunction(neg_reduction (Neg a), neg_reduction (Neg b))

		| UniversialQ _ -> raise (EngineErr "")
		| ExistensialQ _ -> raise (EngineErr "")
		| Implication _ -> raise (EngineErr "")

		| True -> False
		| False -> True
		| _ -> f
	)
	| Conjunction(a, b) -> Conjunction(neg_reduction a, neg_reduction b)
	| Disjunction(a, b) -> Disjunction(neg_reduction a, neg_reduction b)

	| UniversialQ _ -> raise (EngineErr "")
	| ExistensialQ _ -> raise (EngineErr "")
	| Implication _ -> raise (EngineErr "")

	| _ -> f

(* reducing negations on arithmetic terms such as !(x=y) => x>y \/ y>x *)
let rec neg_reduction_arith (f : foltree ) =
	match f with
	| Neg (l) ->
	(
		match l with
		| Identity(a, b) -> Disjunction(Greater(a, b), Greater(b, a))
		| Greater (a, b) -> Disjunction(Greater(b, a), Identity(a, b))
		| _ -> f 
	)
	| Conjunction(a, b) -> Conjunction(neg_reduction_arith a, neg_reduction_arith b)
	| Disjunction(a, b) -> Disjunction(neg_reduction_arith a, neg_reduction_arith b)

	| UniversialQ _ -> raise (EngineErr "")
	| ExistensialQ _ -> raise (EngineErr "")
	| Implication _ -> raise (EngineErr "")

	| _ -> f


(* applying distributive law to build dnf; should be implication free and negation only on literals *)
let rec dnf_distribute (f : foltree) = 
	match f with
	| Disjunction(a, b) -> Disjunction(dnf_distribute a, dnf_distribute b)
	| Conjunction(a, b) -> 
		let x = dnf_distribute a in
		let y = dnf_distribute b in 
		(match x, y with
		| _, Disjunction(l, r) -> Disjunction (dnf_distribute (Conjunction (x, l)), dnf_distribute (Conjunction (x, r)))
		| Disjunction(l,r) , _ ->  Disjunction (dnf_distribute (Conjunction(l, y)), dnf_distribute (Conjunction (r, y)))
		| _, _ -> Conjunction(x,y))

	| UniversialQ _ -> raise (EngineErr "")
	| ExistensialQ _ -> raise (EngineErr "")
	| Implication _ -> raise (EngineErr "")
	| _ -> f

(* test syntactic equality of f1 and f2 *)
let rec fol_syn_eq (f1 : foltree) (f2 : foltree) : bool =
	match f1, f2 with
	|	True, True -> true
	|   False, False -> true
	|   Identity (a, b), Identity (c, d) -> atermtree_eq a c && atermtree_eq b d 
	|   Neg (t1), Neg(t2) -> fol_syn_eq t1 t2
	|   Greater (a, b), Greater (c, d) -> atermtree_eq a c && atermtree_eq b d
	|   Predicate (s1, t1), Predicate (s2, t2) -> s1=s2 && atermtree_eq_list t1 t2
	|   _ -> false

(* test syntactic equality of f1 and f2 *)
let rec fol_syn_eq_list (fl : foltree list) (f : foltree) : bool =
	match fl with
	| t :: l -> if fol_syn_eq t f then true else fol_syn_eq_list l f
	| [] -> false

(* make dnf form of quantifier free f *)
let reduce_to_dnf (f : foltree) =
	dnf_distribute (neg_reduction_arith (neg_reduction (impl_reduction f)))


(**********)
(* make dnf into list of clauses *)
let rec disjunctive_list (f : foltree) : foltree list = 
	match f with
	| Conjunction(a, b) -> disjunctive_list a @ disjunctive_list b
	| _ -> [f]

let rec dnf_to_list (f : foltree) : (foltree list) list = 
	match f with
	| Disjunction(a, b) -> dnf_to_list a @ dnf_to_list b
	| _ -> [disjunctive_list f]



(**********)
(* reduce dnf clauses based on arithmetic facts *)
let rec dnf_arith_reduction (f : foltree list) =
	match f with
	| q :: l -> 
		(match q with
		| Greater(a, b) -> 
			if fol_syn_eq_list l (Identity (a, b)) || fol_syn_eq_list l (Identity(b,a)) || fol_syn_eq_list l (Greater(b,a)) then
			False :: (dnf_arith_reduction l) else q :: (dnf_arith_reduction l)
		
		| Identity(a, b) -> 
			if fol_syn_eq_list l (Greater(a,b)) || fol_syn_eq_list l (Greater (b,a)) 
			then False :: (dnf_arith_reduction l) else q :: (dnf_arith_reduction l)

		| _ -> (q :: (dnf_arith_reduction l)))
	| _ -> []	

let rec dnf_list_arith_reduction (f : (foltree list) list) =
	match f with
	| f :: l -> dnf_arith_reduction f :: dnf_list_arith_reduction l
	| [] -> []


(* reduce dnf clauses based on tautologies *)
let rec dnf_truth_reduction (f : foltree list) =
	match f with
	| q :: l -> (match q with
				| True -> dnf_truth_reduction l
				| _ -> q :: dnf_truth_reduction l
	)
	| _ -> []	

let rec dnf_list_truth_reduction (f : (foltree list) list) =
	match f with
	| f :: l -> 
		if fol_syn_eq_list f False then dnf_list_truth_reduction l else dnf_truth_reduction f :: dnf_list_truth_reduction l
	| [] -> []


(* reduce dnf clauses based on duplications and contradiction *)
let rec dnf_dup_reduction (f : foltree list) =

	match f with
	| q :: l -> 
		(match q with
		| Neg(t) -> if fol_syn_eq_list f t then False :: (dnf_dup_reduction l) else q :: (dnf_dup_reduction l)
		| _ -> if fol_syn_eq_list l q then True :: (dnf_dup_reduction l) else q :: (dnf_dup_reduction l))
	| _ -> []	

let rec dnf_list_dup_reduction (f : (foltree list) list) =
	match f with
	| f :: l -> dnf_dup_reduction f :: dnf_list_dup_reduction l
	| [] -> []

(* f1 <= f2 *)
let rec dnf_sub (f1 : foltree list) (f2 : foltree list) : bool =
	match f1 with
	| f :: l -> if fol_syn_eq_list f2 f then dnf_sub l f2 else false
	| _ -> true

let rec dnf_sup_list (f1 : foltree list) (f2 : (foltree list) list) : bool =
	match f2 with
	| f :: l -> if dnf_sub f f1 then true else dnf_sup_list f1 l
	| _ -> false


let rec dnf_sub_reduction2 (f1 : (foltree list) list) (f2 : (foltree list) list): (foltree list) list =
	match f1 with
	| k :: l -> if dnf_sup_list k l then dnf_sub_reduction2 l f2 else 
(				if dnf_sup_list k f2 then dnf_sub_reduction2 l f2 else
				dnf_sub_reduction2 l (f2@[k])
)
	| [] -> f2


let simplify_dnf (f : (foltree list) list) : (foltree list) list =
	dnf_sub_reduction2 (dnf_list_truth_reduction (dnf_list_arith_reduction (dnf_list_dup_reduction f))) []



(**********)
(* restore dnf as a list into one fol term *)
let rec fol_of_dnf2 (f : (foltree list)) : foltree = 
	match f with
	| v :: [] -> v
	| v :: l -> Conjunction(v, fol_of_dnf2 l)
	| [] -> False

let rec fol_of_dnf3 (f : (foltree list) list) : foltree =
 	match f with
 	| v :: [] -> fol_of_dnf2 v
 	| v :: l -> Disjunction(fol_of_dnf2 v, fol_of_dnf3 l)
 	| [] -> False

let rec prenex_dnf_reduction2 (v : tagged_variable list) (f : (foltree list) list): foltree =
	match v with
	| v :: l -> (match v with
				| (Univ d, s) -> UniversialQ(s, d, prenex_dnf_reduction2 l f)
				| (Exi d, s) -> ExistensialQ(s, d, prenex_dnf_reduction2 l f)
				)
	| [] -> fol_of_dnf3 f

let rec foltree_reduce_quantis (v : tagged_variable list) (f : foltree) : tagged_variable list =
	match v with
	| (j, s) :: l -> if bounded_var_fol f s then ((j,s)::(foltree_reduce_quantis l f)) else (foltree_reduce_quantis l f)
	| _ -> []


let prenex_dnf (f : foltree) = 
	let p = prenex_extract f in
	{ quantifiers = p.quantifiers ; mainfol = reduce_to_dnf (p.mainfol) }

(**********)
(* for any v, make v quantifier free form by prenex conversion 
 * take it into dnf form then apply the dnf reductions and
 * take it back to one fol term
*)
let prenex_dnf_reduction (v : foltree) : foltree =
	let pre = prenex_dnf v in
	let quantis = pre.quantifiers in 
	let form = pre.mainfol in
	let simpl = (simplify_dnf (dnf_to_list (prenex_dnf (form)).mainfol)) in
	let newquantis = foltree_reduce_quantis quantis (fol_of_dnf3 simpl) in
	prenex_dnf_reduction2 newquantis simpl



(**********)
(* simplify quantifiers -> reduce syntactic identical -> reduce truths.
 * further try reducing using DNF reduction.
 * if DNF reduction only increases the number of clauses, 
 * roll back!
 *)
let fol_reduce (f : foltree) : foltree = 
	let simpl = simplify_t (simplify_i (reduce_quantifiers f)) in
	let pr = prenex_dnf_reduction simpl in
	if (size simpl) > (size pr) then pr else simpl


(**********)
(* printings *)
let rec print_tagged_var (v : tagged_variable) = 
	match (fst v) with
	| Univ d -> "U "^(snd v)
	| Exi d -> "E "^(snd v)

let rec print_tagged_var_list (v : tagged_variable list) =
	match v with
	| v :: l -> (print_tagged_var v)^" "^(print_tagged_var_list l)
	| [] -> ""

let print_prenex (p : prenex_form) =
	(print_tagged_var_list (p.quantifiers))^" "^(print_foltree (p.mainfol))

let rec print_dnf (f : foltree list) =
	match f with
	| f :: [] -> (print_foltree f)
	| f :: l -> (print_foltree f)^" /\\ "^(print_dnf l)
	| [] -> ""

let rec print_dnf_list1 (f : (foltree list) list) (i : int)= 
	match f with
	| f :: l -> (string_of_int i)^"] "^(print_dnf f)^"\n\n"^(print_dnf_list1 l (i+1))
	| [] -> ""

let print_dnf_list (f : (foltree list) list) = 
	print_dnf_list1 f 1

