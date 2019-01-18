%{
	open Printf
	open Lexing
	open List
	open Hashtbl
	open Ast 
	open Context
	open Typing
	open Logic
	open Vccalc
	open Reduction
	open Exporter
	open Log
	open Loader
	open Errors
	open Utilities
	let line_pos() = 
		{ infile_line = !curline}


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
   		$1;
		(let ctx : (string, data_type) Hashtbl.t = Hashtbl.create 10 in
    	(match load_input_ctx ctx $4 with
    	| Some ctx -> 
    		(print_endline (print_sem_list $6 ctx))
    	| _ -> print_endline "cannot load context"))

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
		$1;
  		load_program $3 $5 $8 $10 $12;
  		let vc = vc_extract() in
		let simpl = simplify_t (simplify_i (reduce_quantifiers vc)) in
		let clist = split_conjunctions simpl in
		let more_reduced = reduce_quantifiers_list clist in 
		dump_coq more_reduced;
		dump_log();
		print_endline ("\n\n"^(!coqfilename)^".v and "^(!coqfilename)^"_log.txt are created\n\n")
	}
	
	| PRECONDITION fol POSTCONDITION fol INPUT LPAREN typed_variable_list RPAREN statement RETURN term EOF {

		  		load_program $2 $4 $7 $9 $11;
		  		let vc = vc_extract() in
				let simpl = simplify_t (simplify_i (reduce_quantifiers vc)) in
				let clist = split_conjunctions simpl in
				let more_reduced = reduce_quantifiers_list clist in 
				dump_coq more_reduced;
				dump_log();
				print_endline ("\n\n"^(!coqfilename)^".v and "^(!coqfilename)^"_log.txt are created\n\n")

	 };

print_sem_list:
	| SEMANTIC term print_sem_list {$2 :: $3}
	| SEMANTIC term {[$2]}


load_block:
	| loading load_block { $1; $2 }
	| loading { $1 };

loading:
	| LOAD ID COLON typelist EQ GT LR spec_list { if load_mfun $2 ($4, Real) then load_mfun_spec $2 ($4, Real) $8 else raise (LoadFail $2) }
	| LOAD ID COLON typelist EQ GT LZ spec_list { if load_mfun $2 ($4, Int) then load_mfun_spec $2 ($4, Int) $8 else raise (LoadFail $2) }
	| LOAD ID COLON typelist IMPL LR spec_list { if load_sfun $2 ($4, Real) then load_sfun_spec $2 ($4, Real) $7 else raise (LoadFail $2) }
	| LOAD ID COLON typelist IMPL LZ spec_list { if load_sfun $2 ($4, Int) then load_sfun_spec $2 ($4, Int) $7 else	raise (LoadFail $2) }
	| DEFINITION ID COLON typelist IMPL PROP ASSIGN fol { load_pdefi $2 $4 $8 }

	| ASSUME COQ DOT { coq_theories := $2 :: !coq_theories }
	| ASSUME fol { load_theories [$2] };

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
	| statement SEQ statement { Sequence_pre (line_pos(), $1, $3) }
	| NEWVAR ID ASSIGN term { Newvariable_pre (line_pos(), $2, $4) }
	| ID ASSIGN term { Assignment_pre (line_pos(), $1, $3) }
	| ID LBRACK term RBRACK ASSIGN term { ArrayAssign_pre (line_pos(), $1, $3, $6)}
	| IF term THEN statement ELSE statement { Conditional_pre (line_pos(), $2, $4, $6) }
	| INVARIANT fol VARIANT lterm WHILE term DO statement { Whileloop_pre (line_pos(), $6, $8, $2, $4) }
	| LBLOCK statement LBLOCK { $2 };

term_list:
	| term { [$1] }
	| term COMMA term_list { $1::$3 }

term:
	| NUM RCONS { RConst_pre (line_pos(), $1) }
	| NUM { Const_pre (line_pos(), $1) }
	| term EQ term { Eq_pre(line_pos(), $1, $3) }
	| term GT term { Gt_pre(line_pos(), $1, $3) }
	| term LT term { Gt_pre(line_pos(), $3, $1) }
	| term PLUS term { Plus_pre (line_pos(), $1, $3) }
	| MINUS term { Minus_pre (line_pos(), $2) }
	| term MULT term { Mult_pre (line_pos(), $1, $3) }
	| DIV term { Div_pre (line_pos(), $2) }
	| term MINUS term { Plus_pre (line_pos(), $1, Minus_pre (line_pos(), $3)) }
	| term DIV term { Mult_pre (line_pos(), $1, Div_pre (line_pos(), $3)) }
	| MAX LPAREN term COMMA term RPAREN { Max_pre(line_pos(), $3, $5) }
	| TEST LPAREN term RPAREN { Test_pre (line_pos(), $3) }
	| ID LBRACK term RBRACK { Access_pre (line_pos(), $1, $3) }
	| ID LPAREN term_list RPAREN { Application_pre(line_pos(), $1, $3) }
	| ID { Variable_pre (line_pos(), $1) }

	| SELECT LPAREN term_list RPAREN { Select_pre(line_pos(), $3) }
	| term AND term { And_pre (line_pos(), $1, $3) }
	| term OR term { Or_pre (line_pos(), $1, $3) }
	| NEG term { Neg_pre (line_pos(), $2) }
	| AT term QUEST term COLON term { Inlinecond_pre (line_pos(), $2, $4, $6) } 

	| IOTA LPAREN term RPAREN { Iota_pre (line_pos(), $3) }

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
	| lterm EQ lterm { Identity_pre (line_pos(), $1, $3) }
	| lterm GT lterm { Greater_pre (line_pos(), $1, $3) }
	
	| lterm LT lterm { LT_pre (line_pos(), $1, $3) }
	| lterm GT EQ lterm { GE_pre (line_pos(), $1, $4) }
	| lterm LT EQ lterm { LE_pre (line_pos(), $1, $4) }
	| lterm LT lterm LT lterm { LTLT_pre (line_pos(), $1, $3, $5) }
	| lterm LT EQ lterm LT lterm { LELT_pre (line_pos(), $1, $4, $6) }
	| lterm LT lterm LT EQ lterm { LTLE_pre (line_pos(), $1, $3, $6) }
	| lterm LT EQ lterm LT EQ lterm { LELE_pre (line_pos(), $1, $4, $7) }
	| lterm GT lterm GT lterm { GTGT_pre (line_pos(), $1, $3, $5) }
	| lterm GT EQ lterm GT lterm { GEGT_pre (line_pos(), $1, $4, $6) }
	| lterm GT lterm GT EQ lterm { GTGE_pre (line_pos(), $1, $3, $6) }
	| lterm GT EQ lterm GT EQ lterm { GEGE_pre (line_pos(), $1, $4, $7) }

	| ID LBRACK lterm_list RBRACK { Predicate_pre (line_pos(), $1, $3) }
	| fol IMPL fol { Implication_pre (line_pos(), $1, $3) }
	| fol DISJ fol { Disjunction_pre (line_pos(), $1, $3) }
	| fol CONJ fol { Conjunction_pre (line_pos(), $1, $3) }
	| FORALL ID COLON ltype COMMA fol { UniversialQ_pre (line_pos(), $2, $4, $6) }
	| EXISTS ID COLON ltype COMMA fol { ExistensialQ_pre (line_pos(), $2, $4, $6) }
	| EXISTS EXCLAM ID COLON ltype COMMA fol { UniqQ_pre (line_pos(), $3, $5, $7) 	}
	| LPAREN fol RPAREN { $2 }
	| TRUE { True_pre (line_pos()) }
	| FALSE { False_pre (line_pos()) };

lterm:
	| lterm PLUS lterm { APlus_pre (line_pos(), $1, $3) }
	| lterm MULT lterm { AMult_pre (line_pos(), $1, $3) }
	| MINUS lterm { AMinus_pre (line_pos(), $2) }
	| DIV lterm { ADiv_pre (line_pos(), $2) }
	| lterm MINUS lterm { APlus_pre (line_pos(), $1, AMinus_pre (line_pos(), $3)) }
	| lterm DIV lterm { AMult_pre (line_pos(), $1, ADiv_pre (line_pos(), $3)) }
	| LPAREN lterm RPAREN { $2 }
	| ID { AVariable_pre (line_pos(), $1) }
	| PREC LPAREN lterm RPAREN { Prec_pre (line_pos(), $3) }
	| ID LPAREN lterm_list RPAREN { AApplication_pre (line_pos(), $1, $3)  }
	| UNDERBAR { AVariable_pre (line_pos(), "@res") }
	| NUM RCONS { ARConst_pre (line_pos(), $1) }
	| NUM { AZConst_pre (line_pos(), $1) }
	| AT NUM { AVariable_pre (line_pos(), "@"^(string_of_int $2)) }
	;

lterm_list:
	| lterm { [$1] }
	| lterm COMMA lterm_list { $1 :: $3 }

ltype:
	| LR { Real }
	| LZ { Int }

%%







