open Hashtbl
open Ast
exception Illtyped of string
exception TermTypeError of ((string, data_type) Hashtbl.t) * termtree
exception StatementTypeError of ((string, data_type) Hashtbl.t) * statementtree
exception AtermTypeError of ((string, data_type) Hashtbl.t) * atermtree
exception FolTypeError of ((string, data_type) Hashtbl.t) * foltree
exception TypingError of (string * string * (string, data_type) Hashtbl.t)
exception PlainError of string
exception UnQuant of string
exception LoadFail of string

(* unintended engine error... *)
exception EngineErr of string

(* user fault errors; it will be called when we type check user provided erc program*)
exception TypeInferErrAterm of aterm_pre
exception TypeInferErrFol of fol_pre
exception TypeInferErr of term_pre
exception TypeInferErrStmt of statement_pre

