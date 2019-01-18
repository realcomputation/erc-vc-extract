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
