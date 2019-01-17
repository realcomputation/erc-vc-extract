(* Canonical form a atermtree *)
open Ast
open Logic


type rational = int * int
let radd (r1 : rational) (r2 : rational) = ((fst r1) * (snd r2) + (snd r1) * (fst r2), (snd r1) * (snd r2))
let rmult (r1 : rational) (r2 : rational) = ((fst r1) * (fst r2), (snd r1) * (snd r2))

type real_linear = ((rational * string) list) * rational
type int_linear = ((int * string) list) * int



let rec print_linear2 (r : (rational * string) list) =
	match r with
	| ((n, d), s) :: [] -> "("^(string_of_int n)^","^(string_of_int d)^")"^s
	| ((n, d), s) :: l -> "("^(string_of_int n)^","^(string_of_int d)^")"^s^"+"^(print_linear2 l)
	| [] -> ""

let rec print_linear (r : real_linear) =
	let (l,(n, d)) = r in
	"("^(string_of_int n)^","^(string_of_int d)^") + "^(print_linear2 l)

let rec clean_atermtree_linear2 (c : (rational * string) list) =
	match c with
	| ((a,b), v) :: l -> if a = 0 then clean_atermtree_linear2 l else ((a,b),v) :: (clean_atermtree_linear2 l)
	| [] -> []

let clean_atermtree_linear (c : real_linear) =
	(clean_atermtree_linear2 (fst c), snd c)



let rec clean_int_linear2 (c : (int * string) list) =
	match c with
	| (k, v) :: l -> if k=0 then clean_int_linear2 l else (k, v) :: (clean_int_linear2 l)
	| [] -> []

let clean_int_linear (c : int_linear) =
	(clean_int_linear2 (fst c), snd c)



let rec merge_int_linear2 (c1 : (int * string) list) (c2 : (int * string) list) : (int * string) list =
	match c1, c2 with
	| (k1, v1) :: cl1, (k2, v2) :: cl2 ->
		if v2 < v1 then (k2, v2) :: merge_int_linear2 c1 cl2
		else
			(
			if v1<v2 then (k1, v1) :: merge_int_linear2 c2 cl1
			else (k1+k2, v1) :: merge_int_linear2 cl1 cl2 
			)
	| _, [] -> c1
	| [], _ -> c2

let merge_int_linear (c1 : int_linear) (c2 : int_linear) : int_linear =
	let ans = 
	(merge_int_linear2 (fst c1) (fst c2), (snd c1) + (snd c2))
	in
	ans


let rec negate_int_linear2 (c : (int * string) list) =
	match c with
	| (k, v) :: l -> (-k, v) :: (negate_int_linear2 l)
	| _ -> []

let negate_int_linear (c : int_linear) : int_linear =
	let (l, c0) = c in
	(negate_int_linear2 l, -c0)



let rec merge_atermtree_linear2 (c1 : (rational * string) list) (c2 : (rational * string) list) : (rational * string) list =
	match  c1,  c2 with
	| (k1, v1) :: cl1, (k2, v2) :: cl2 -> if v2 < v1 then (k2, v2) :: merge_atermtree_linear2 c1 cl2 
										else (if v1 < v2 then (k1, v1) :: merge_atermtree_linear2 c2 cl1 else
										(radd k1 k2, v1) :: merge_atermtree_linear2 cl1 cl2)
	| _, [] -> c1
	| [], _ -> c2

let merge_atermtree_linear (c1 : real_linear) (c2 : real_linear) : real_linear =
	let ans = 
	(merge_atermtree_linear2 (fst c1) (fst c2), radd (snd c1) (snd c2))
	in
	ans

let rec mult_atermtree_linear3 (c1 : (rational * string) list) (c : rational) : (rational * string) list =
	match c1 with
	| (k, v) :: cl -> (rmult k c, v) :: mult_atermtree_linear3 cl c
	| [] -> []


let rec mult_atermtree_linear2 (c1 : real_linear) (c : rational) : real_linear =
	(mult_atermtree_linear3 (fst c1) c, rmult (snd c1) c)

let mult_atermtree_linear (c1 : real_linear) (c2 : real_linear) : real_linear option =
	let c1 = clean_atermtree_linear c1 in
	let c2 = clean_atermtree_linear c2 in
	(match fst c1, fst c2 with
		| [], _ -> Some (mult_atermtree_linear2 c2 (snd c1))
		| _, [] -> Some (mult_atermtree_linear2 c1 (snd c2))
		| _, _ -> None)


let rec atermtree_linear_canonical (a : atermtree) :  real_linear option =
	match a with
	| APlus(x, y) -> 	
		let l1 = atermtree_linear_canonical x in
		let l2 = atermtree_linear_canonical y in
		(match l1, l2 with
		| Some l1, Some l2 -> Some (merge_atermtree_linear l1 l2)
		| _ -> None
		)
	| AMult(x, y) ->
		let l1 = atermtree_linear_canonical x in
		let l2 = atermtree_linear_canonical y in
		(match l1, l2 with
		| Some l1, Some l2 -> mult_atermtree_linear l1 l2
		| _ -> None
		)
	| AVariable(v) -> Some ([((1,1),v)], (0,1))
	| ARConst(z) -> Some ([], (z,1))
	| AMinus(z) -> 
		let l = atermtree_linear_canonical z in
		(match l with
		| Some l -> mult_atermtree_linear l ([],(-1,1))
		| _ -> None
		)
	| ADiv(z) -> 
		let l = atermtree_linear_canonical z in
		(match l with
		| Some ([], (r1, r2)) -> Some ([], (r2, r1)) 
		| _ -> None)

	| _ -> None

let rec int_linear_canonical (a : atermtree) : int_linear option =
	match a with
	| APlus (x, y) -> 
		let l1 = int_linear_canonical x in
		let l2 = int_linear_canonical y in
		(match l1, l2 with
		| Some l1, Some l2 -> Some (merge_int_linear l1 l2)
		| _, _ -> None
		)
	| AVariable v -> Some ([(1,v)], 0)
	| AZConst z -> Some ([], z)
	| AMinus z ->
		let l = int_linear_canonical z in
		(match l with
		| Some l -> Some (negate_int_linear l)
		| _ -> None
		)
	| _ -> None



let rec find_var_linear2 (a : (rational * string) list) (v : string) : rational * ((rational * string) list) =
	match a with
	| (k, s) :: l -> if v = s then (k, l) else
						let (kp, lp) = find_var_linear2 l v in
						(kp, (k,s)::lp)
	| [] -> ((0,1), a)

let find_var_linear (a : real_linear) ( s: string) : (rational * real_linear) =
	let (k, l) = find_var_linear2 (fst a) s in
	(k, (l, snd a))


let rec atermtree_of_linear2 (a : (rational * string) list) : atermtree =
	match a with 
	| ((n, d), s) :: [] -> AMult(AMult(ARConst n, ADiv (ARConst d)), AVariable s)
	| ((n, d), s) :: l -> APlus(AMult(AMult(ARConst n, ADiv (ARConst d)), AVariable s), atermtree_of_linear2 l)
	| [] -> ARConst 0

let rec atermtree_of_linear (a : real_linear) : atermtree =
	let (l, (n,d)) = a in
	APlus(atermtree_of_linear2 l, AMult(ARConst n, ADiv (ARConst d)))

(* infer s = ~~ when a = 0 is assumed*)
let find_var_linear_identity (a : real_linear) (s : string) : atermtree option =
	let ((n, d), l) = find_var_linear a s in
	match n with
	| 0 -> None
	| _ -> Some  (atermtree_of_linear (mult_atermtree_linear2 l (-d, n)))




(* find v in a canonical form *)
let rec find_var_int2 (a : (int * string) list) (v : string) : int * ((int * string) list) =
	match a with
	| (k, s) :: l -> if v = s then (k, l) else
						let (kp, lp) = find_var_int2 l v in
						(kp, (k,s)::lp)
	| [] -> (0, a)

let find_var_int (a : int_linear) (s: string) : (int * int_linear) =
	let (k, l) = find_var_int2 (fst a) s in
	(k, (l, snd a))

let rec atermtree_of_int2 (a : (int * string) list) : atermtree =
	match a with 
	| (k, s) :: [] -> AMult(AZConst k, AVariable s)
	| (k, s) :: l -> APlus(AMult(AZConst k, AVariable s), atermtree_of_int2 l)
	| [] -> AZConst 0

let rec atermtree_of_int (a : int_linear) : atermtree =
	let (l, k) = a in
	APlus(atermtree_of_int2 l, AZConst k)

let find_var_int_identity (a : int_linear) (s : string) : atermtree option =
	let (k, l) = find_var_int a s in
	match k with
	|  1 -> Some (atermtree_of_int (negate_int_linear l))
	| -1 -> Some (atermtree_of_int l)
	| _  -> None




