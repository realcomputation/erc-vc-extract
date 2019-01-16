open Hashtbl
open Ast
exception Illtyped of string
exception TermTypeError of ((string, data_type) Hashtbl.t) * termtree
exception StatementTypeError of ((string, data_type) Hashtbl.t) * statementtree
exception AtermTypeError of ((string, data_type) Hashtbl.t) * aterm
exception FolTypeError of ((string, data_type) Hashtbl.t) * foltree
exception TypingError of (string * string * (string, data_type) Hashtbl.t)
exception PlainError of string
exception UnQuant of string
exception LoadFail of string
