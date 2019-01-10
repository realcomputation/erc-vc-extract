open Hashtbl
open Datatype
open Ast
open Errors

(** Check whether v is bounded  *)
let rec bounded_var_aterm (a : aterm) (v : string) : bool = 
	match a with
	|   Prec t -> (bounded_var_aterm t v)
	|   APlus (t1, t2) -> ((bounded_var_aterm t1 v) || (bounded_var_aterm t2 v))
	|   AMult (t1, t2) -> ((bounded_var_aterm t1 v) || (bounded_var_aterm t2 v))
	|   ADiv t ->  (bounded_var_aterm t v)
	|   AMinus t -> (bounded_var_aterm t v)
	|   AApplication (s, tl) -> bounded_var_aterm_list tl v
	|   AVariable s -> s = v
	|   _ -> false

and bounded_var_aterm_list (a : aterm list) (v : string): bool = 
	match a with
	| a :: l -> bounded_var_aterm a v || bounded_var_aterm_list l v
	| [] -> false

let rec bounded_var_fol (ft : foltree) (v : string) : bool =
	match ft with
	| Neg (f) -> (bounded_var_fol f v)
	| Identity (t1, t2) ->  (bounded_var_aterm t1 v || bounded_var_aterm t2 v)
	| Greater (t1, t2) -> (bounded_var_aterm t1 v || bounded_var_aterm t2 v)
	| Implication (f1, f2) -> (bounded_var_fol f1 v || bounded_var_fol f2 v)
	| UniversialQ (s, t, f) -> bounded_var_fol f v
	| ExistensialQ (s, t, f) -> bounded_var_fol f v
	| Disjunction (f1, f2) -> (bounded_var_fol f1 v || bounded_var_fol f2 v)
	| Conjunction (f1, f2) -> (bounded_var_fol f1 v || bounded_var_fol f2 v)
	| Predicate (s, tl) -> bounded_var_aterm_list tl v
	| _ -> false




(* Replacement and Application *)
let rec aterm_application (at : aterm) (x : aterm) : aterm =
	match at with
	|   Prec t -> Prec (aterm_application t x)
	|   APlus (t1, t2) -> APlus ((aterm_application t1 x), (aterm_application t2 x))
	|   AMult (t1, t2) -> AMult ((aterm_application t1 x), (aterm_application t2 x))
	|   ADiv t -> ADiv (aterm_application t x)
	|   AMinus t -> AMinus (aterm_application t x)	
	|   AApplication (s, tl) -> AApplication (s, aterm_application_list tl x)
	|   AProjection (s, t) -> AProjection (aterm_application s x, aterm_application t x)
	|   ASub (s, t, e) -> ASub (aterm_application s x, aterm_application t x, aterm_application e x)
	|   AInput -> x
	|   _ -> at

and aterm_application_list (at : aterm list) (x : aterm) : aterm list =
	match at with
	| a :: l -> (aterm_application a x) :: (aterm_application_list l x)
	| [] -> []

(** replace @input in ft into x *)
let rec fol_application (ft : foltree) (x : aterm) : foltree =
	match ft with
	| Neg (f) -> Neg (fol_application f x)
	| Identity (t1, t2) -> Identity (aterm_application t1 x, aterm_application t2 x)
	| Greater (t1, t2) -> Greater (aterm_application t1 x, aterm_application t2 x)
	| Implication (f1, f2) -> Implication (fol_application f1 x, fol_application f2 x)
	| UniversialQ (s, t, f) -> UniversialQ (s, t, fol_application f x)
	| ExistensialQ (s, t, f) -> ExistensialQ (s, t, fol_application f x)
	| Disjunction (f1, f2) -> Disjunction (fol_application f1 x, fol_application f2 x)
	| Conjunction (f1, f2) -> Conjunction (fol_application f1 x, fol_application f2 x)
	| Predicate (s, tl) -> Predicate(s, aterm_application_list tl x)
	| _ -> ft


(** replace Variable v -> q in p *)
let rec aterm_replace (at : aterm) (v : string) (x : aterm) =
	match at with
	|   Prec t -> Prec (aterm_replace t v x)
	|   APlus (t1, t2) -> APlus ((aterm_replace t1 v x), (aterm_replace t2 v x))
	|   AMult (t1, t2) -> AMult ((aterm_replace t1 v x), (aterm_replace t2 v x))
	|   ADiv t -> ADiv (aterm_replace t v x)
	|   AMinus t -> AMinus (aterm_replace t v x)	
	|   AApplication (s, tl) -> AApplication (s, aterm_replace_list tl v x)

(*  array can be replaced with other array variables *)
	|   AProjection (s, t) -> AProjection (aterm_replace s v x, aterm_replace t v x)
	|   ASub (s, t, e) -> ASub (aterm_replace s v x, aterm_replace t v x, aterm_replace e v x)

	|   AVariable s -> if (s = v) then x else at
	|   _ -> at

and aterm_replace_list (at : aterm list) (v : string) (x : aterm) : aterm list =
	match at with
	| a :: l -> (aterm_replace a v x) :: (aterm_replace_list l v x)
	| [] -> []

let rec fol_replace (ft : foltree) (v : string) (x : aterm) : foltree =
	match ft with
	| Neg (f) -> Neg (fol_replace f v x)
	| Identity (t1, t2) -> Identity (aterm_replace t1 v x, aterm_replace t2 v x)
	| Greater (t1, t2) -> Greater (aterm_replace t1 v x, aterm_replace t2 v x)
	| Implication (f1, f2) -> Implication (fol_replace f1 v x, fol_replace f2 v x)
	| UniversialQ (s, t, f) -> UniversialQ (s, t, fol_replace f v x)
	| ExistensialQ (s, t, f) -> ExistensialQ (s, t, fol_replace f v x)
	| Disjunction (f1, f2) -> Disjunction (fol_replace f1 v x, fol_replace f2 v x)
	| Conjunction (f1, f2) -> Conjunction (fol_replace f1 v x, fol_replace f2 v x)
	| Predicate (s, tl) -> Predicate (s, aterm_replace_list tl v x)
	| _ -> ft

let rec fol_replace_list (ft : foltree) (v : (string * aterm) list) : foltree = 
	match v with
	| (v, x) :: l -> fol_replace_list (fol_replace ft v x) l
	| [] -> ft





(** check whether a contains @ *)
let rec is_predicate_aterm (a : aterm) : bool = 
	match a with
	|   Prec t -> (is_predicate_aterm t)
	|   APlus (t1, t2) -> ((is_predicate_aterm t1) || (is_predicate_aterm t2))
	|   AMult (t1, t2) -> ((is_predicate_aterm t1) || (is_predicate_aterm t2))
	|   ADiv t ->  (is_predicate_aterm t)
	|   AMinus t -> (is_predicate_aterm t)
	|   AApplication (s, tl) -> is_predicate_aterm_list tl
	|   AInput -> true
	|   _ -> false

and is_predicate_aterm_list (a : aterm list) : bool = 
	match a with
	| a :: l -> is_predicate_aterm a || is_predicate_aterm_list l
	| [] -> false

(** check whether a contains @ *)
let rec is_predicate_fol (ft : foltree) : bool =
	match ft with
	| Neg (f) -> (is_predicate_fol f)
	| Identity (t1, t2) ->  (is_predicate_aterm t1 || is_predicate_aterm t2)
	| Greater (t1, t2) -> (is_predicate_aterm t1 || is_predicate_aterm t2)
	| Implication (f1, f2) -> (is_predicate_fol f1 || is_predicate_fol f2)
	| UniversialQ (s, t, f) -> is_predicate_fol f
	| ExistensialQ (s, t, f) -> is_predicate_fol f
	| Disjunction (f1, f2) -> (is_predicate_fol f1 || is_predicate_fol f2)
	| Conjunction (f1, f2) -> (is_predicate_fol f1 || is_predicate_fol f2)
	| Predicate (s, tl) -> is_predicate_aterm_list tl
	| _ -> false


	
(* check two aterms are syntactically equal *)
let rec aterm_eq (a1 : aterm) (a2 : aterm) : bool = 
	match a1, a2 with
	| AZConst z1, AZConst z2 -> z1 = z2
	| ARConst z1, ARConst z2 -> z1 = z2
	| Prec z1, Prec z2 -> aterm_eq z1 z2
	| APlus (z1, z2), APlus (z3, z4) -> aterm_eq z1 z3 && aterm_eq z2 z4
	| AMult (z1, z2), AMult (z3, z4) -> aterm_eq z1 z3 && aterm_eq z2 z4
	| ADiv z1, ADiv z2 -> aterm_eq z1 z2
	| AMinus z1, AMinus z2 -> aterm_eq z1 z2
	| AVariable s1, AVariable s2 -> s1 = s2
	| AApplication (s1, l1), AApplication (s2, l2) -> s1 = s2 && aterm_eq_list l1 l2
	| AInput, AInput -> true
	| _, _ -> false
and aterm_eq_list (a1 : aterm list) (a2 : aterm list) : bool =
	match a1, a2 with
	| a1 :: l1, a2 :: l2 -> aterm_eq a1 a2 && aterm_eq_list l1 l2
	| [], [] -> true
	| _, _ -> false




