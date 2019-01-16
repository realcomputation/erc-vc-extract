open Hashtbl

(* Data types *)
type data_type =
		Real 
	|   Int
	|   Reala of int
	|   Inta of int

type typed_variable = data_type * string

(* AST of Assertion Languages *)
type aterm =
		AZConst of int
	|   ARConst of int
	|   Prec of aterm
	|   APlus of aterm * aterm
	|   AMult of aterm * aterm
	|   ADiv of aterm
	|   AMinus of aterm
	|   AVariable of string
	|   AApplication of string * (aterm list)
	|   AProjection of aterm * aterm
	|   ASub of aterm * aterm * aterm
	|   AInput

type foltree = 
		True
	|   False
	|   Identity of aterm * aterm
	|   Neg of foltree
	|   Greater of aterm * aterm
	|   Implication of foltree * foltree
	|   UniversialQ of string * data_type * foltree
	|   ExistensialQ of string * data_type * foltree
	|   Disjunction of foltree * foltree
	|   Conjunction of foltree * foltree
	|   Predicate of string * (aterm list) 

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
	|   Whileloop of termtree * statementtree * foltree * aterm 


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





(* Utilities: Printing AST *)
let print_type (t : data_type) =
	match t with
	| Real -> "\\mathbb{R}"
	| Int -> "\\mathbb{Z}"
	| Reala d -> "R("^(string_of_int d)^")"
	| Inta d -> "Z("^(string_of_int d)^")"


let rec print_aterm (at : aterm)=
	match at with 
	|	AZConst z -> (string_of_int z)
	|   ARConst z -> (string_of_int z)^".0"
	|   Prec z -> ("2^"^ (print_aterm z))
	|   APlus (t1, t2) -> "("^(print_aterm t1)^" + "^(print_aterm t2)^")"
	|   AMult (t1, t2) -> "("^(print_aterm t1)^" * "^(print_aterm t2)^")"
	|   ADiv (t) -> "/ "^(print_aterm t)
	|   AMinus (t) -> "- "^(print_aterm t)
	|   AVariable s -> s
	|   AApplication (s, l) -> s^"("^(print_aterm_list l)^")"
	|   AProjection (s, i) -> (print_aterm s)^"["^(print_aterm i)^"]" 
	|   ASub (s, t, e) -> (print_aterm s)^"["^(print_aterm t)^"=>"^(print_aterm e)^"]"
	|   AInput -> "@"

and print_aterm_list (al : aterm list) =
	match al with
	| v :: [] -> (print_aterm v)
	| v :: l -> (print_aterm v)^", "^(print_aterm_list l)
	| _ -> ""

let rec print_foltree (f : foltree) = 
	match f with
	|	True -> "True"
	|   False -> "False"
	|   Identity (t1, t2) -> "("^(print_aterm t1)^"="^(print_aterm t2)^")"
	|   Neg (f1) -> "(!"^(print_foltree f1)^")"
	|   Greater (t1, t2) -> "("^(print_aterm t1)^">"^(print_aterm t2)^")"
	|   Implication (f1, f2) -> "("^(print_foltree f1)^" \\to "^(print_foltree f2)^")"
	|   UniversialQ (s, dt, f) -> "(\\forall "^s^" : "^(print_type dt)^", "^(print_foltree f)^")"
	|   ExistensialQ (s, dt, f) -> "(\\exists "^s^" : "^(print_type dt)^", "^(print_foltree f)^")"
	|   Disjunction (f1, f2) -> "("^(print_foltree f1)^" \\lor "^(print_foltree f2)^")"
	|   Conjunction (f1, f2) -> "("^(print_foltree f1)^" \\land "^(print_foltree f2)^")"
	|   Predicate (s, tl) -> s^"("^(print_aterm_list tl)^")"

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




