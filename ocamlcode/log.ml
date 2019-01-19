(**********)
(* erc-vc-extract is a OCaml written program that 
 * extracts verification conditions of an annotated ERC program
 * written by Sewon Park @ KAIST (2019).
 *
 * log.ml: the file is a part of erc-vc-extract contains
 * a global variable which contains procedure of quantifier reductions
*)
let reduction_log : string ref =  ref ""
