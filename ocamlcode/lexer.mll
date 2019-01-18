{
	open Parser
	open Lexing
	open Utilities
	(* updating position *)
	let pos lexbuf = (lexeme_start lexbuf, lexeme_end lexbuf)
	let new_line2 pos = { pos with pos_lnum = pos.pos_lnum + 1; pos_bol = pos.pos_cnum; }
	let new_line lexbuf = curline := !curline + 1; lexbuf.lex_curr_p <- new_line2 lexbuf.lex_curr_p
}

let digit = ['0'-'9']
let ident = ['a'-'z' 'A'-'Z']
let ident_num = ['a'-'z' 'A'-'Z' '0'-'9' '_']



rule token = parse
	| "(*" { comment lexbuf }

	(* Ignore blanks *)
  	| [' ' '\t' ] { token lexbuf }
  	| '\n' { new_line lexbuf; token lexbuf }
  	
  	| digit+ as num { NUM(int_of_string num) }

  	| ".0" { RCONS }

  	(* ERC Program *)
  	| "Input" { INPUT }
  	| "Return" { RETURN }

  	(* ERC Statements *)
  	| "if" { IF }
  	| "then" { THEN }
  	| "else" { ELSE }
  	| "while" { WHILE }
  	| "do" { DO }
  	| ";" { SEQ }
  	| ":=" { ASSIGN }
  	| "newvar" { NEWVAR }

	| '{' { LBLOCK }
	| '}' { RBLOCK } 
	| '[' { LBRACK } 
	| ']' { RBRACK } 	
	| '(' { LPAREN }
	| ')' { RPAREN }
	| ',' { COMMA }
	| ':' { COLON }
	| '_' { UNDERBAR }

	(* ERC Types *)
	| "Real" { REAL }
	| "Integer" { INT }

	(* ERC Terms *)
	| '>' { GT }
	| '<' { LT }
	| '-' { MINUS }
	| '*' { MULT }
	| '/' { DIV }
	| '+' { PLUS }
	| '=' { EQ }
	| '?' { QUEST }
	| '!' { EXCLAM }
	| "select" { SELECT }
	| "iota" { IOTA }
	| "test" { TEST }
	| "max" { MAX }
	| "||" { OR }
	| "&&" { AND }
	| "!" { NEG }

	(* fol *)
	| '.' { DOT }
	(* Assertion language *)
	| "when" { WHEN }
	| "with" { WITH }
	| "@precondition" { PRECONDITION }
	| "@postcondition" { POSTCONDITION }
	| "@invariant" { INVARIANT }
	| "@variant" { VARIANT }
	| "@load" { LOAD }
	| "@definition" { DEFINITION }
	| "@context" { CONTEXT }
	| "@semantic" { SEMANTIC }
	| "@assume" { ASSUME }
	| "@Coq" { coq lexbuf  }
	| "Prop" { PROP }
	| '@' { AT }

	(* Logical Symbols *)
	| "forall" { FORALL }
	| "exists" { EXISTS }
	| "/\\" { CONJ }
	| "\\/" { DISJ }  
	| "->" { IMPL }
	| "True" { TRUE }
	| "False" { FALSE }
	| "prec" { PREC }

	| '|' { BAR }

	(* fol type *)
	| 'R' { LR }
	| 'Z' { LZ }
	| "@res" { LRESULT }

	(* Variables *)
	| ident_num+ as id { ID id}

	(* Go to Other Rules *)
	| eof { EOF }

and comment = parse
	| "*)" { token lexbuf }
	| "\n" {new_line lexbuf; comment lexbuf }
	| _ { comment lexbuf }
	| eof { EOF }

and coq = parse
	| '.' { token lexbuf }
	| '\n' { new_line lexbuf; coq lexbuf }
	| [ ^'.' ]+ as coqc { COQ coqc }
	| eof { EOF }





