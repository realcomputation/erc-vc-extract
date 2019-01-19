(**********)
(* erc-vc-extract is a OCaml written program that 
 * extracts verification conditions of an annotated ERC program
 * written by Sewon Park @ KAIST (2019).
 *
 * utilities.ml: the file is a part of erc-vc-extract contains
 * basic functions that to be used by the program.
 * bind_list _ f is a functor action on a function f by the list monad.
 * it should be declared in OCaml standard library... but i wrote it myself here since
 * it will take shorter than searching it...
 * curline is a global variable stores current line of parser; it is not appropriate to be here;
 * it should be moved to other files in future version of development.
*)
exception ListErr of string

let rec bind_list a f =
	match a with
	| v::l -> f v :: bind_list l f
	| [] -> []

let rec unfold_list a f g =
	match a with
	| v :: l -> g v (unfold_list l f g)
	| [] -> f

let rec merge_list a b =
	match a, b with
	| a::l1, b::l2 -> (a, b) :: (merge_list l1 l2)
	| [],[] -> []
	| _, _ -> raise (ListErr "merging list of different size")

let rec split_list a =
	match a with
	| (c, d) :: l -> let k = split_list l in (c :: fst k, d :: snd k)	
	| [] -> ([], [])
let curline : int ref = ref 0
