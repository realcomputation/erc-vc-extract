%{
	open Printf
	open Lexing
	open List
	open Hashtbl
	open Ast 
	open Context
	open Typing
	open Logic
	open Wpcalc
	open Reduction
	open Exporter
	open Log
	open Errors
%}
%token EOF

/*
	ERC Program related tokens
*/
%token INPUT RETURN

/*
	ERC Statement related tokens
*/
%token IF THEN ELSE WHILE DO SEQ ASSIGN NEWVAR

/*
	ERC Datatype related tokens
*/
%token REAL REALA INT INTA 

/*
	ERC Structure related tokens
*/
%token LBRACK RBRACK LPAREN RPAREN LBLOCK RBLOCK COMMA COLON AT RCONS

/*
	ERC Term related tokens
*/
%token GT LT PLUS MINUS MULT DIV SELECT QUEST IOTA MAX TEST 

%token AND OR NEG


/*
	Assertion language: First Order Logik
*/
%token FORALL EXISTS CONJ DISJ IMPL TRUE FALSE LEQ LGT DOT EQ BAR WHEN EXCLAM UNDERBAR ASSUME

/*
	Assertion 
*/
%token PRECONDITION POSTCONDITION INVARIANT VARIANT LOAD DEFINITION PROP LR LZ LRESULT WITH LVAlUE PREC

%token CONTEXT SEMANTIC

%token <int> NUM

%token <string> ID 

%token <string> COQ


%nonassoc GT LT
%nonassoc EQ
%left PLUS
%left MULT
%left OR
%left AND
%left DIV
%left MINUS
%left NEG
%nonassoc LBRACK RBRACK
%left SEQ

%left CONJ
%left DISJ
%left IMPL
%nonassoc COMMA 

%nonassoc WHILE DO IF THEN ELSE QEUST COLON AT

%start prog
%type <unit> prog

%%
prog: 

    | load_block CONTEXT LPAREN typed_variable_list RPAREN print_sem_list EOF { 
    	if $1 then 
		(let ctx : (string, data_type) Hashtbl.t = Hashtbl.create 10 in
    	(match load_input_ctx ctx $4 with
    	| Some ctx -> 
    		(print_endline (print_sem_list $6 ctx))
    	| _ -> print_endline "cannot load context")) else (print_endline "cannot load assumptions")

    }

    | CONTEXT LPAREN typed_variable_list RPAREN print_sem_list EOF { 
		(let ctx : (string, data_type) Hashtbl.t = Hashtbl.create 10 in
    	(match load_input_ctx ctx $3 with
    	| Some ctx -> 
    		(print_endline (print_sem_list $5 ctx))
    	| _ -> print_endline "cannot load context")) 
    }

    | load_block 
	  PRECONDITION fol POSTCONDITION fol INPUT LPAREN typed_variable_list RPAREN statement RETURN term EOF 
	{

	  	if $1 
	  	then 
	  		(
		  		let fol_list = wp_run $3 $5 $8 $10 $12 in
				let simpl = simplify_t (simplify_i (reduce_quantifiers fol_list)) in
				let clist = split_conjunctions simpl in
				let more_reduced = reduce_quantifiers_list clist in 
				dump_coq $8 $10 $12 $3 $5 more_reduced;
				dump_log();
				print_endline ("\n\n"^(!coqfilename)^".v and "^(!coqfilename)^"_log.txt are created\n\n")
			)
		else 
			print_endline "assumptions cannot be loaded"
	}
	
	| PRECONDITION fol POSTCONDITION fol INPUT LPAREN typed_variable_list RPAREN statement RETURN term EOF {

		  		let fol_list = wp_run $2 $4 $7 $9 $11 in
				let simpl = simplify_t (simplify_i (reduce_quantifiers fol_list)) in
				let clist = split_conjunctions simpl in
				let more_reduced = reduce_quantifiers_list clist in 
				dump_coq $7 $9 $11 $2 $4 (more_reduced);
				dump_log();
				print_endline ("\n\n"^(!coqfilename)^".v and "^(!coqfilename)^"_log.txt are created\n\n")

	 };

print_sem_list:
	| SEMANTIC term print_sem_list {$2 :: $3}
	| SEMANTIC term {[$2]}


load_block:
	| loading load_block { $1 && $2 }
	| loading { $1 };

loading:
	| LOAD ID COLON typelist EQ GT LR spec_list { if load_mfun $2 ($4, Real) && load_mfunfol $2 ($4, Real) $8 then true else 
		raise (LoadFail $2)}
	| LOAD ID COLON typelist EQ GT LZ spec_list { if load_mfun $2 ($4, Int) && load_mfunfol $2 ($4, Int) $8 then true else 
		raise (LoadFail $2)}
	| LOAD ID COLON typelist IMPL LR spec_list { if load_sfun $2 ($4, Real) && load_sfunfol $2 ($4, Real) $7 then true else 
		raise (LoadFail $2)}
	| LOAD ID COLON typelist IMPL LZ spec_list { if load_sfun $2 ($4, Int) && load_sfunfol $2 ($4, Int) $7 then true else 
		raise (LoadFail $2)}
	| DEFINITION ID COLON typelist IMPL PROP ASSIGN fol { if load_pdefi $2 $4 $8 then true else 
		raise (LoadFail $2)}

	| ASSUME COQ DOT { coq_theories := $2 :: !coq_theories; true }

	| ASSUME fol { if load_theories [$2] then true else 
		raise (LoadFail (print_foltree $2)) };

spec_list:
	| spec { [$1] }
	| spec BAR spec_list { $1 :: $3 }

spec:
	| WHEN fol WITH fol { ($2, $4) }


typelist:
	| ltype { [$1] }
	| ltype MULT typelist { $1 :: $3 }



/* Programming language */
statement:
	| statement SEQ statement { Sequence ($1, $3) }
	| NEWVAR ID ASSIGN term { Newvariable ($2, $4) }
	| ID ASSIGN term { Assignment ($1, $3) }
	| ID LBRACK term RBRACK ASSIGN term { ArrayAssign ($1, $3, $6)}
	| IF term THEN statement ELSE statement { Conditional ($2, $4, $6) }
	| INVARIANT fol VARIANT lterm WHILE term DO statement { Whileloop ($6, $8, $2, $4) }
	| LBLOCK statement LBLOCK { $2 };

term_list:
	| term { [$1] }
	| term COMMA term_list { $1::$3 }

term:
	| NUM RCONS { RConst $1 }
	| NUM { Const $1 }
	| term EQ term { Eq($1, $3) }
	| term GT term { Gt($1, $3) }
	| term LT term { Gt($3, $1) }
	| term PLUS term { Plus ($1, $3) }
	| MINUS term { Minus $2 }
	| term MULT term { Mult ($1, $3) }
	| DIV term { Div $2 }
	| term MINUS term { Plus($1, Minus $3) }
	| term DIV term { Mult($1, Div $3) }
	| MAX LPAREN term COMMA term RPAREN { Max($3, $5) }
	| TEST LPAREN term RPAREN { Test ($3) }
	| ID LBRACK term RBRACK { Access ($1, $3) }
	| ID LPAREN term_list RPAREN { Application($1, $3) }
	| ID { Variable $1 }

	| SELECT LPAREN term_list RPAREN { Select($3) }
	| term AND term { And ($1, $3) }
	| term OR term { Or ($1, $3) }
	| NEG term { Neg $2 }
	| AT term QUEST term COLON term { Inlinecond ($2, $4, $6) } 

	| IOTA LPAREN term RPAREN { Iota $3 }

	| LPAREN term RPAREN { $2 };

typed_variable_list:
	| typed_variable_list COMMA typed_variable { $3 :: $1 }
	| typed_variable { [$1] };

typed_variable:
	| ID COLON dtype { ($3, $1) };

dtype:
	| REAL LPAREN NUM RPAREN { Reala($3) }
	| INT  LPAREN NUM RPAREN { Inta($3) }
	| REAL { Real }
	| INT { Int };



/* assertion language */
fol:
	| lterm EQ lterm { Identity ($1, $3) }
	| lterm GT EQ lterm { Disjunction (Greater($1, $4), Identity($1,$4)) }
	| lterm GT lterm { Greater ($1, $3) }
	| lterm LT lterm { Greater ($3, $1)}
	| lterm LT EQ lterm { Disjunction (Greater($4, $1), Identity($1,$4)) }
	
	| lterm LT lterm LT lterm { Conjunction(Greater($5, $3), Greater($3, $1)) }
	| lterm LT EQ lterm LT lterm { Conjunction(Disjunction(Greater($4, $1), Identity($4,$1)), Greater($6, $4)) }
	| lterm LT lterm LT EQ lterm { Conjunction(Greater($3, $1), Disjunction(Greater($6, $3), Identity($6, $3))) }
	| lterm LT EQ lterm LT EQ lterm { Conjunction(Disjunction(Greater ($4, $1), Identity($4,$1)), Disjunction(Greater($7,$4), Identity($7,$4)))}
	| lterm GT lterm GT lterm { Conjunction(Greater($1,$3), Greater($3, $5)) } 
	| lterm GT EQ lterm GT lterm { Conjunction(Disjunction(Greater($1,$4),Identity($1,$4)), Greater($4,$6)) }
	| lterm GT lterm GT EQ lterm { Conjunction(Greater($1,$3), Disjunction(Greater($3,$6), Identity($3,$6))) }
	| lterm GT EQ lterm GT EQ lterm { Conjunction(Disjunction(Greater($1,$4), Identity($1,$4)), Disjunction(Greater($4,$7), Identity($4,$7))) }

	| ID LBRACK lterm_list RBRACK { Predicate($1, $3) }
	| fol IMPL fol { Implication ($1, $3) }
	| fol DISJ fol { Disjunction ($1, $3) }
	| fol CONJ fol { Conjunction ($1, $3) }
	| FORALL ID COLON ltype COMMA fol { UniversialQ ($2, $4, $6) }
	| EXISTS ID COLON ltype COMMA fol { ExistensialQ ($2, $4, $6) }
	| EXISTS EXCLAM ID COLON ltype COMMA fol { 
		let w = ("_uniq"^($3)^(string_of_int (!freshvar +1))) in
		(freshvar := !freshvar+1);
		ExistensialQ ($3, $5, Conjunction($7, 
			UniversialQ(w, $5, Implication(fol_replace $7 $3 (AVariable w), Identity (AVariable $3, AVariable w)))))
 	}
	| LPAREN fol RPAREN { $2 }
	| TRUE { True }
	| FALSE { False };

lterm:
	| lterm PLUS lterm { APlus ($1, $3) }
	| lterm MULT lterm { AMult ($1, $3) }
	| MINUS lterm { AMinus $2 }
	| DIV lterm { ADiv $2 }
	| lterm MINUS lterm { APlus ($1, AMinus $3) }
	| lterm DIV lterm { AMult ($1, ADiv $3) }
	| LPAREN lterm RPAREN { $2 }
	| ID { AVariable $1}
	| PREC LPAREN lterm RPAREN { Prec $3 }
	| ID LPAREN lterm_list RPAREN { AApplication ($1, $3)  }
	| UNDERBAR { AVariable "@res" }
	| NUM RCONS { ARConst $1 }
	| NUM { AZConst $1 }
	| AT NUM { AVariable ("@"^(string_of_int $2)) }
	;

lterm_list:
	| lterm { [$1] }
	| lterm COMMA lterm_list { $1 :: $3 }

ltype:
	| LR { Real }
	| LZ { Int }

%%







