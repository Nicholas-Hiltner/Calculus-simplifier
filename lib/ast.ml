(** The type of binary operators. *)
type bop = 
    | Add
    | Subt
    | Mult
    | Div
    | Pow

(** The type of the abstract syntax tree (AST). *)
type 'a expr =
    | Var of 'a
    | Fun of string * ('a expr) list
    | Int of int
    | Binop of bop * ('a expr) * ('a expr)
    | Ddx of 'a * ('a expr)

type 'a rule = Rule of ('a expr * 'a expr)