(**********)
(* erc-vc-extract is a OCaml written program that 
 * extracts verification conditions of an annotated ERC program
 * written by Sewon Park @ KAIST (2019).
 *
 * ast.ml: the file is a part of erc-vc-extract contains
 * abstract syntax trees of ERC.
 * the one ends with _pre is used to represent user given ERC program which is not
 * type-checked yet. 
*)
open Hashtbl
open Utilities
(* Data types *)
type data_type =
		Real 
	|   Int
	|   Reala of int
	|   Inta of int

type typed_variable = data_type * string


type infilepos = { infile_line : int }

let print_infile (t : infilepos) : string =
	(string_of_int (t.infile_line ))

(* pre - ast with in-file position tagged. *)
type aterm_pre =
		AZConst_pre of infilepos * int
	|   ARConst_pre of infilepos * int
	|   Prec_pre of infilepos * aterm_pre
	|   APlus_pre of infilepos * aterm_pre * aterm_pre
	|   AMult_pre of infilepos * aterm_pre * aterm_pre
	|   ADiv_pre of infilepos * aterm_pre
	|   AMinus_pre of infilepos * aterm_pre
	|   AVariable_pre of infilepos * string
	|   AApplication_pre of infilepos * string * (aterm_pre list)
	|   AProjection_pre of infilepos * aterm_pre * aterm_pre
	|   ASub_pre of infilepos * aterm_pre * aterm_pre * aterm_pre
	|   AInput_pre of infilepos

type fol_pre = 
		True_pre of infilepos
	|   False_pre of infilepos
	|   Identity_pre of infilepos * aterm_pre * aterm_pre
	|   Neg_pre of infilepos * fol_pre
	|   Greater_pre of infilepos * aterm_pre * aterm_pre
	|   Implication_pre of infilepos * fol_pre * fol_pre
	|   UniversialQ_pre of infilepos * string * data_type * fol_pre
	|   ExistensialQ_pre of infilepos * string * data_type * fol_pre
	|   Disjunction_pre of infilepos * fol_pre * fol_pre
	|   Conjunction_pre of infilepos * fol_pre * fol_pre
	|   Predicate_pre of infilepos * string * (aterm_pre list) 
(* that does not appear in ast *)
	|   UniqQ_pre of infilepos * string * data_type * fol_pre 
	|   LT_pre of infilepos * aterm_pre * aterm_pre
	|   GE_pre of infilepos * aterm_pre * aterm_pre
	|   LE_pre of infilepos * aterm_pre * aterm_pre
	|   GTGT_pre of infilepos * aterm_pre * aterm_pre * aterm_pre
	|   GTGE_pre of infilepos * aterm_pre * aterm_pre * aterm_pre
	|   GEGT_pre of infilepos * aterm_pre * aterm_pre * aterm_pre
	|   GEGE_pre of infilepos * aterm_pre * aterm_pre * aterm_pre
	|   LTLT_pre of infilepos * aterm_pre * aterm_pre * aterm_pre
	|   LTLE_pre of infilepos * aterm_pre * aterm_pre * aterm_pre
	|   LELT_pre of infilepos * aterm_pre * aterm_pre * aterm_pre
	|   LELE_pre of infilepos * aterm_pre * aterm_pre * aterm_pre

(* 	| lterm GT EQ lterm { Disjunction (Greater($1, $4), Identity($1,$4)) }
	| lterm LT EQ lterm { Disjunction (Greater($4, $1), Identity($1,$4)) }
	| lterm LT lterm LT lterm { Conjunction(Greater($5, $3), Greater($3, $1)) }
	| lterm LT EQ lterm LT lterm { Conjunction(Disjunction(Greater($4, $1), Identity($4,$1)), Greater($6, $4)) }
	| lterm LT lterm LT EQ lterm { Conjunction(Greater($3, $1), Disjunction(Greater($6, $3), Identity($6, $3))) }
	| lterm LT EQ lterm LT EQ lterm { Conjunction(Disjunction(Greater ($4, $1), Identity($4,$1)), Disjunction(Greater($7,$4), Identity($7,$4)))}
	| lterm GT lterm GT lterm { Conjunction(Greater($1,$3), Greater($3, $5)) } 
	| lterm GT EQ lterm GT lterm { Conjunction(Disjunction(Greater($1,$4),Identity($1,$4)), Greater($4,$6)) }
	| lterm GT lterm GT EQ lterm { Conjunction(Greater($1,$3), Disjunction(Greater($3,$6), Identity($3,$6))) }
	| lterm GT EQ lterm GT EQ lterm { Conjunction(Disjunction(Greater($1,$4), Identity($1,$4)), Disjunction(Greater($4,$7), Identity($4,$7))) }
 *)


type term_pre = 
		Variable_pre of infilepos * string
	|   Const_pre of infilepos * int
	|   RConst_pre of infilepos * int
	(*	Arithmetic operators *)
	|   Mult_pre of infilepos * term_pre * term_pre
	|   Div_pre of infilepos * term_pre	
	|   Plus_pre of infilepos * term_pre * term_pre
	|   Minus_pre of infilepos * term_pre
	(*	Boolean related operations *)	
	|   Gt_pre of infilepos * term_pre * term_pre
	|   Eq_pre of infilepos * term_pre * term_pre
	|   Neg_pre of infilepos *  term_pre
	|   And_pre of infilepos * term_pre * term_pre
	|   Or_pre of infilepos * term_pre * term_pre
	(*	Primitive functions *)
	|   Select_pre of infilepos * term_pre list
	|   Iota_pre of infilepos * term_pre
	|   Max_pre of infilepos * term_pre * term_pre
	|   Inlinecond_pre of infilepos * term_pre * term_pre * term_pre
	(*	ETC *)
	|   Access_pre of infilepos * string * term_pre
	|   Application_pre of infilepos * string * (term_pre list)
	|   Test_pre of infilepos * term_pre

type statement_pre =
		Empty_pre of infilepos 
	|   Sequence_pre of infilepos * statement_pre * statement_pre
	|   Newvariable_pre of infilepos * string * term_pre
	|   Assignment_pre of infilepos * string * term_pre
	|   ArrayAssign_pre of infilepos * string * term_pre * term_pre
	|   Conditional_pre of infilepos * term_pre * statement_pre * statement_pre
	|   Whileloop_pre of infilepos * term_pre * statement_pre * fol_pre * aterm_pre 





(* AST of Assertion Languages *)
type atermtree =
		AZConst of int
	|   ARConst of int
	|   Prec of atermtree
	|   APlus of atermtree * atermtree
	|   AMult of atermtree * atermtree
	|   ADiv of atermtree
	|   AMinus of atermtree
	|   AVariable of string
	|   AApplication of string * (atermtree list)
	|   AProjection of atermtree * atermtree
	|   ASub of atermtree * atermtree * atermtree
	|   AInput

type foltree = 
		True
	|   False
	|   Identity of atermtree * atermtree
	|   Neg of foltree
	|   Greater of atermtree * atermtree
	|   Implication of foltree * foltree
	|   UniversialQ of string * data_type * foltree
	|   ExistensialQ of string * data_type * foltree
	|   Disjunction of foltree * foltree
	|   Conjunction of foltree * foltree
	|   Predicate of string * (atermtree list) 

(* AST of ERC Programming Language *)
type termtree = 
		Variable of string
	|   Const of int
	|   RConst of int
	(*	Arithmetic operators *)
	|   Mult of termtree * termtree
	|   Div of termtree	
	|   Plus of termtree * termtree
	|   Minus of termtree
	(*	Boolean related operations *)	
	|   Gt of termtree * termtree
	|   Eq of termtree * termtree
	|   Neg of  termtree
	|   And of termtree * termtree
	|   Or of termtree * termtree
	(*	Primitive functions *)
	|   Select of termtree list
	|   Iota of termtree
	|   Max of termtree * termtree
	|   Inlinecond of termtree * termtree * termtree
	(*	ETC *)
	|   Access of string * termtree
	|   Application of string * (termtree list)
	|   Test of termtree

type statementtree =
		Empty 
	|   Sequence of statementtree * statementtree
	|   Newvariable of string * termtree
	|   Assignment of string * termtree
	|   ArrayAssign of string * termtree * termtree
	|   Conditional of termtree * statementtree * statementtree
	|   Whileloop of termtree * statementtree * foltree * atermtree 


type termtree_typed =
		Variable_typed of data_type * string
	|   Const_typed of data_type * int
	|   RConst_typed of data_type * int
	(*	Arithmetic operators *)
	|   Mult_typed of data_type * termtree * termtree
	|   Div_typed of data_type * termtree	
	|   Plus_typed of data_type * termtree * termtree
	|   Minus_typed of data_type * termtree
	(*	Boolean related operations *)	
	|   Gt_typed of data_type * termtree * termtree
	|   Eq_typed of data_type * termtree * termtree
	|   Neg_typed of data_type *  termtree
	|   And_typed of data_type * termtree * termtree
	|   Or_typed of data_type * termtree * termtree
	(*	Primitive functions *)
	|   Select_typed of data_type * termtree list
	|   Iota_typed of data_type * termtree
	|   Max_typed of data_type * termtree * termtree
	|   Inlinecond_typed of data_type * termtree * termtree * termtree
	(*	ETC *)
	|   Access_typed of data_type * string * termtree
	|   Application_typed of data_type * string * (termtree list)
	|   Test_typed of data_type * termtree




(* Utilities: constructing fol from/to list *)
let rec existence_from_list (s : typed_variable list) (f : foltree) =
	match s with 
	| (d, v) :: l -> ExistensialQ(v, d, existence_from_list l f)
	| [] -> f

let rec universial_from_list (s : typed_variable list) (f : foltree) =
	match s with 
	| (d, v) :: l -> UniversialQ(v, d, universial_from_list l f)
	| [] -> f

let rec list_to_conj (f : foltree list) =
	match f with
	| f :: [] -> f
	| f :: l -> Conjunction(f, list_to_conj l)
	| [] -> True

let rec list_to_disj (f : foltree list) = 
	match f with
	| f :: [] -> f
	| f :: l -> Disjunction(f, list_to_disj l)
	| [] -> True

let impl_list (f : (foltree * foltree) list) : foltree list = 
	bind_list f (fun k -> Implication(fst k, snd k))




(* Utilities: Printing AST *)
let print_type (t : data_type) =
	match t with
	| Real -> "R"
	| Int -> "Z"
	| Reala d -> "R("^(string_of_int d)^")"
	| Inta d -> "Z("^(string_of_int d)^")"

let rec print_aterm_pre (at : aterm_pre) =
	match at with 
	|	AZConst_pre (p,z)  -> (p, (string_of_int z))
	|   ARConst_pre (p,z)  -> (p, (string_of_int z))
	|   Prec_pre (p,z)  -> (p, ("2^"^ (snd (print_aterm_pre z))))
	|   APlus_pre (p, t1, t2) -> (p, "("^(snd (print_aterm_pre t1))^" + "^(snd (print_aterm_pre t2))^")")
	|   AMult_pre (p, t1, t2) -> (p, "("^(snd (print_aterm_pre t1))^" * "^(snd (print_aterm_pre t2))^")")
	|   ADiv_pre (p, t) -> (p, "/ "^(snd (print_aterm_pre t)))
	|   AMinus_pre (p, t) -> (p, "- "^(snd (print_aterm_pre t)))
	|   AVariable_pre (p, s)  -> (p, s)
	|   AApplication_pre (p, s, l) -> (p, s^"("^(unfold_list (bind_list l (fun l -> snd (print_aterm_pre l))) "" (fun a b -> a^" "^b))^")")
	|   AProjection_pre (p, s, i) -> (p, (snd (print_aterm_pre s))^"["^(snd (print_aterm_pre i))^"]" )
	|   ASub_pre (p, s, t, e) -> (p, (snd (print_aterm_pre s))^"["^(snd (print_aterm_pre t))^"=>"^(snd (print_aterm_pre e))^"]")
	|   AInput_pre p -> (p, "@")

let rec print_fol_pre (f : fol_pre) = 
	match f with
	|	True_pre p -> (p, "True")
	|   False_pre p -> (p, "False")
	|   Identity_pre (p, t1, t2) -> (p, "("^(snd (print_aterm_pre t1))^"="^(snd (print_aterm_pre t2))^")")
	|   Neg_pre (p, f1) -> (p, "(!"^(snd (print_fol_pre f1))^")")
	|   Greater_pre (p, t1, t2) -> (p, "("^(snd (print_aterm_pre t1))^">"^(snd (print_aterm_pre t2))^")")
	|   Implication_pre (p, f1, f2) -> (p, "("^(snd (print_fol_pre f1))^" \\to "^(snd (print_fol_pre f2))^")")
	|   UniversialQ_pre (p, s, dt, f) -> (p, "(\\forall "^s^" : "^(print_type dt)^", "^(snd (print_fol_pre f))^")")
	|   ExistensialQ_pre (p, s, dt, f) -> (p, "(\\exists "^s^" : "^(print_type dt)^", "^(snd (print_fol_pre f))^")")
	|   Disjunction_pre (p, f1, f2) -> (p, "("^(snd (print_fol_pre f1))^" \\lor "^(snd (print_fol_pre f2))^")")
	|   Conjunction_pre (p, f1, f2) -> (p, "("^(snd (print_fol_pre f1))^" \\land "^(snd (print_fol_pre f2))^")")
	|   Predicate_pre (p, s, tl) -> (p, s^"("^(unfold_list (bind_list tl (fun l -> snd (print_aterm_pre l))) "" (fun a b -> a^" "^b))^")")
	|   _ -> ({infile_line=1}, "cannot print")

let rec print_term_pre (tterm : term_pre) =
	match tterm with
	|	Variable_pre (p, z)  -> (p, z)
	|   Const_pre (p, z)  -> (p, (string_of_int z))
	|   RConst_pre (p, z)  -> (p, (string_of_int z))
(*	arithmetic operations... maybe it will be better to have these categorized *)
	|   Mult_pre (p, t1, t2) -> (p, (snd (print_term_pre t1))^" * "^(snd (print_term_pre t2)))
	|   Plus_pre (p, t1, t2) -> (p, (snd (print_term_pre t1))^" + "^(snd (print_term_pre t2)))
	|   Minus_pre (p, t)  -> (p, "-"^(snd (print_term_pre t)))
	|   Div_pre (p, t)  -> (p, "/"^(snd (print_term_pre t)))
(*	Boolean related operations *)	
	|   Gt_pre (p, t1, t2) -> (p, (snd (print_term_pre t1)) ^">"^(snd (print_term_pre t2)))
	|   Eq_pre (p, t1, t2) -> (p, (snd (print_term_pre t1)) ^"="^(snd (print_term_pre t2)))
	|   Neg_pre (p, t) -> (p, (snd (print_term_pre t)))
	|   And_pre (p, t1, t2) -> (p, (snd (print_term_pre t1))^" && "^(snd (print_term_pre t2)))
	|   Or_pre (p, t1, t2) -> (p, (snd (print_term_pre t1)) ^"||"^ (snd (print_term_pre t2)))
(*	Primitive functions *)
	|   Select_pre (p, tl) -> (p, "Choose("^(unfold_list (bind_list tl (fun l -> snd (print_term_pre l))) "" (fun a b -> a^" "^b))^")")
	|   Iota_pre (p, t) -> (p, "iota("^(snd (print_term_pre t))^")")
	|   Max_pre (p, t1, t2) -> (p, "max("^(snd (print_term_pre t1))^", "^(snd (print_term_pre t2))^")")
	|   Inlinecond_pre (p, t1, t2, t3) -> (p, (snd (print_term_pre t1))^"?"^(snd (print_term_pre t2))^":"^(snd (print_term_pre t3)))
(*	ETC *)
	|   Access_pre (p, s, t) -> (p, (s)^"["^(snd (print_term_pre t))^"]")
	|   Application_pre (p, s, t) -> (p, s^"("^(unfold_list (bind_list t (fun l -> snd (print_term_pre l))) "" (fun a b -> a^" "^b))^")")
	|   Test_pre (p, z) -> (p, "test("^(snd (print_term_pre z))^")")


let rec print_statement_pre (s : statement_pre) =
	match s with
	| Empty_pre p -> (p, "empty")
	| Sequence_pre (p, s1, s2) -> (p, "("^(snd (print_statement_pre s1))^";"^(snd (print_statement_pre s2))^")")
	| Newvariable_pre (p, v, t) -> (p, "new var "^v^" := "^(snd (print_term_pre t)))
	| ArrayAssign_pre (p, s, t, e) -> (p, ("assign ")^s^"["^(snd (print_term_pre t))^"] := "^(snd (print_term_pre e)))
	| Assignment_pre (p, v, t) -> (p, "assign "^v^" := "^(snd (print_term_pre t)))
	| Conditional_pre (p, b, s1, s2) -> (p, "if("^(snd (print_term_pre b))^") then "^(snd (print_statement_pre s1))^" else "^(snd (print_statement_pre s2)))
	| Whileloop_pre (p, b, s, i , v) -> (p, "while "^(snd (print_term_pre b))^" do "^(snd (print_statement_pre s)))



let rec print_atermtree (at : atermtree)=
	match at with 
	|	AZConst z -> (string_of_int z)
	|   ARConst z -> (string_of_int z)^".0"
	|   Prec z -> ("2^"^ (print_atermtree z))
	|   APlus (t1, t2) -> "("^(print_atermtree t1)^" + "^(print_atermtree t2)^")"
	|   AMult (t1, t2) -> "("^(print_atermtree t1)^" * "^(print_atermtree t2)^")"
	|   ADiv (t) -> "/ "^(print_atermtree t)
	|   AMinus (t) -> "- "^(print_atermtree t)
	|   AVariable s -> s
	|   AApplication (s, l) -> s^"("^(print_atermtree_list l)^")"
	|   AProjection (s, i) -> (print_atermtree s)^"["^(print_atermtree i)^"]" 
	|   ASub (s, t, e) -> (print_atermtree s)^"["^(print_atermtree t)^"=>"^(print_atermtree e)^"]"
	|   AInput -> "@"

and print_atermtree_list (al : atermtree list) =
	match al with
	| v :: [] -> (print_atermtree v)
	| v :: l -> (print_atermtree v)^", "^(print_atermtree_list l)
	| _ -> ""

let rec print_foltree (f : foltree) = 
	match f with
	|	True -> "True"
	|   False -> "False"
	|   Identity (t1, t2) -> "("^(print_atermtree t1)^"="^(print_atermtree t2)^")"
	|   Neg (f1) -> "(!"^(print_foltree f1)^")"
	|   Greater (t1, t2) -> "("^(print_atermtree t1)^">"^(print_atermtree t2)^")"
	|   Implication (f1, f2) -> "("^(print_foltree f1)^" \\to "^(print_foltree f2)^")"
	|   UniversialQ (s, dt, f) -> "(\\forall "^s^" : "^(print_type dt)^", "^(print_foltree f)^")"
	|   ExistensialQ (s, dt, f) -> "(\\exists "^s^" : "^(print_type dt)^", "^(print_foltree f)^")"
	|   Disjunction (f1, f2) -> "("^(print_foltree f1)^" \\lor "^(print_foltree f2)^")"
	|   Conjunction (f1, f2) -> "("^(print_foltree f1)^" \\land "^(print_foltree f2)^")"
	|   Predicate (s, tl) -> s^"("^(print_atermtree_list tl)^")"

let rec print_foltree_list (f : foltree list) = 
	match f with
	| f1 :: l -> print_foltree f1 :: print_foltree_list l
	| [] -> []

let rec print_ttree (t : termtree) =
	match t with
	|	Variable s -> s
	|   Const z -> (string_of_int z)
	|   RConst z -> (string_of_int z)
(*	arithmetic operations... maybe it will be better to have these categorized *)
	|   Mult (t1, t2) -> (print_ttree t1)^" * "^(print_ttree t2)
	|   Plus (t1, t2) -> (print_ttree t1)^" + "^(print_ttree t2)
	|   Minus t -> "-"^(print_ttree t)
	|   Div t -> "/"^(print_ttree t)
(*	Boolean related operations *)	
	|   Gt (t1, t2) -> (print_ttree t1) ^">"^(print_ttree t2)
	|   Eq (t1, t2) -> (print_ttree t1) ^"="^(print_ttree t2)
	|   Neg (t) -> (print_ttree t)
	|   And (t1, t2) -> (print_ttree t1)^" && "^(print_ttree t2)
	|   Or (t1, t2) -> (print_ttree t1) ^"||"^ (print_ttree t2)
(*	Primitive functions *)
	|   Select (tl) -> "Choose("^(print_ttree_list tl)^")"
	|   Iota (t) -> "iota("^(print_ttree t)^")"
	|   Max (t1, t2) -> "max("^(print_ttree t1)^", "^(print_ttree t2)^")"
	|   Inlinecond (t1, t2, t3) -> (print_ttree t1)^"?"^(print_ttree t2)^":"^(print_ttree t3)
(*	ETC *)
	|   Access (s, t) -> (s)^"["^(print_ttree t)^"]"
	|   Application (s, t) -> s^"("^(print_ttree_list t)^")"
	|   Test (z) -> "test("^(print_ttree z)^")"

and print_ttree_list (tl : termtree list) =
	match tl with
	| t :: [] -> (print_ttree t)
	| t :: l -> (print_ttree t)^", "^(print_ttree_list l)
	| [] -> ""

let rec print_stree (s : statementtree) =
	match s with
	| Empty -> "empty"
	| Sequence (s1, s2) -> "("^(print_stree s1)^";"^(print_stree s2)^")"
	| Newvariable (v, t) -> "new var "^v^" := "^(print_ttree t)
	| ArrayAssign (s, t, e) -> ("assign ")^s^"["^(print_ttree t)^"] := "^(print_ttree e)
	| Assignment (v, t) -> "assign "^v^" := "^(print_ttree t)
	| Conditional (b, s1, s2) -> "if("^(print_ttree b)^") then "^(print_stree s1)^" else "^(print_stree s2)
	| Whileloop (b, s, i , v) -> "while "^(print_ttree b)^" do "^(print_stree s)

type nat = O | S of nat
let rec indentation (t : nat) =
	match t with
	| S n -> " "^(indentation n)
	| _ -> ""

let rec print_stree_ind (s : statementtree) (n : nat) =
	match s with
	| Empty -> (indentation n)^"empty"
	| Sequence (s1, s2) -> (print_stree_ind s1 n)^"\n"^(print_stree_ind s2 n)
	| Newvariable (v, t) -> (indentation n)^"Newvar "^v^" := "^(print_ttree t)
	| Assignment (v, t) -> (indentation n)^"assign "^v^" := "^(print_ttree t)
	| ArrayAssign (s, t, e) -> (indentation n)^("assign ")^s^"["^(print_ttree t)^"] := "^(print_ttree e)
	| Conditional (b, s1, s2) -> (indentation n)^"if("^(print_ttree b)^")\n"^
								 (indentation n)^"then\n"^(print_stree_ind s1 (S n))^"\n"^(indentation n)^"else\n"^(print_stree_ind s2 (S n))
	| Whileloop (b, s, i , v) -> (indentation n)^"while ("^(print_ttree b)^")\n"^(indentation n)^"do\n"^(print_stree_ind s (S n))

let rec print_stree_ind_comment (s : statementtree) (n : nat) =
	match s with
	| Empty -> (indentation n)^"empty"
	| Sequence (s1, s2) -> (print_stree_ind_comment s1 n)^"\n *"^(print_stree_ind_comment s2 n)
	| Newvariable (v, t) -> (indentation n)^"Newvar "^v^" := "^(print_ttree t)
	| Assignment (v, t) -> (indentation n)^"assign "^v^" := "^(print_ttree t)
	| ArrayAssign (s, t, e) -> (indentation n)^("assign ")^s^"["^(print_ttree t)^"] := "^(print_ttree e)
	| Conditional (b, s1, s2) -> (indentation n)^"if("^(print_ttree b)^")\n *"^
								 (indentation n)^"then\n *"^(print_stree_ind_comment s1 (S n))^"\n *"^(indentation n)^"else\n *"^(print_stree_ind_comment s2 (S n))
	| Whileloop (b, s, i , v) -> (indentation n)^"while ("^(print_ttree b)^")\n *"^(indentation n)^"do\n *"^(print_stree_ind_comment s (S n))



let rec size (f : foltree) : int =
	match f with
	|	True -> 1
	|   False -> 1
	|   Identity _ -> 1
	|   Neg z -> size z
	|   Greater _ -> 1
	|   Implication (a, b) -> (size a) + (size b)
	|   UniversialQ (a, b, c) -> size c
	|   ExistensialQ (a, b, c) -> size c
	|   Disjunction (a, b) -> (size a) + (size b)
	|   Conjunction (a, b) -> (size a) + (size b)
	|   Predicate _ -> 1 




