open Hashtbl

(* Data types *)
type data_type =
		Real 
	|   Int
	|   Reala of int
	|   Inta of int

type typed_variable = data_type * string