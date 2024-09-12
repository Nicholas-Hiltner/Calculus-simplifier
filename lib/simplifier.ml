open Ast
open Modules

let showOp =
    function 
    | Subt -> "-"
    | Add -> "+"
    | Mult -> "*"
    | Div -> "/"
    | Pow -> "^"

let rec showExpr =
    function
    | Fun (f, lst) -> f^"("^String.concat "," (List.map showExpr lst) ^")"
    | Int i -> string_of_int i
    | Var i -> i
    | Binop (op,l,r) -> showExprParens l ^ showOp op ^ showExprParens r
    | Ddx (v,e) -> "d/d"^v^" "^showExprParens e
and showExprParens e =
    match e with 
    | Binop _ -> "("^showExpr e ^")"
    | Ddx _ -> "("^showExpr e ^")"
    | _ -> showExpr e

let printExpr e = print_endline (showExpr e)

module SubMap = Map.Make(String)

module Substitution = struct

    type 'a substitution = ('a expr) SubMap.t

    let singleton (x : string) (e : 'a expr) : 'a substitution = SubMap.(empty |> add x e)

    let empty : 'a substitution = SubMap.empty

    let for_all (f : string -> 'a expr -> bool) (subst : 'a substitution) : bool = SubMap.for_all f subst

    let combine_substitutions (a : 'a substitution option) (b : 'a substitution option) : 'a substitution option =
        let no_inc_dups a b =
            let rec b_dups (ak, av) b =
                match b with
                | [] -> true
                | (bk, bv) :: t -> 
                    if ak <> bk then b_dups (ak, av) t 
                    else 
                    if bv <> av then false
                    else b_dups (ak, av) t
            in
            let rec a_dups a b =
                match a with
                | [] -> true
                | h :: t -> if b_dups h b then a_dups t b else false
            in
            a_dups a b
        in
        match (a, b) with
        | (Some a, Some b) ->
            let a_pairs = SubMap.bindings a
            and b_pairs = SubMap.bindings b
            in
            if no_inc_dups a_pairs b_pairs 
                then Some (SubMap.union (fun _ v1 _ -> Some v1) a b)
                else None
        | (_, _) -> None


    exception MalformedSubstitution of string

    let rec substitute (subst : 'a substitution) (pattern : string expr) : 'a expr =
        match pattern with
        | Fun (f, lst) -> Fun (f, List.map (fun x -> substitute subst x) lst)
        | Int i -> Int i
        | Binop (op, l, r) -> Binop (op, substitute subst l, substitute subst r)
        | Ddx (v, e) -> (
            match SubMap.find v subst with
            | Var x -> Ddx (x, substitute subst e) 
            | _ -> raise @@ MalformedSubstitution v
        )
        | Var x -> SubMap.find x subst

    let print_sub a =
        let rec print_pairs =
            function
            | [] -> ()
            | (a, b) :: t ->
                print_string a;
                print_string " -> ";
                printExpr b;
                print_pairs t
        in
        print_pairs @@ SubMap.bindings a
end

(** [parseExpr s] parses [s] into an AST. *)
let parseExpr (s : string) : string expr =
    let lexbuf = Lexing.from_string s in
    let ast = Parser.prog Lexer.read lexbuf in
    ast

(** [parseRule s] parses [s] into a rule. *)
let parseRule (s : string) : string rule =
    let lexbuf = Lexing.from_string s in
    let ast = Parser.rule Lexer.read lexbuf in
    ast

module ApplyRuleM = ApplyRule (Substitution)

let rec apply_rules expr =
    function 
    | [] -> None
    | ((x,desc)::xs) -> (match ApplyRuleM.apply_rule x expr with
    | None -> apply_rules expr xs
    | Some v -> Some (v,desc))

(** apply_to_nf [rules] [expr]
    applies the rules in [rules] to [expr] until no more rules can be applied *)
let rec apply_to_nf rules expr =
    match (apply_rules expr (List.combine rules rules)) with
    | None -> []
    | (Some (e,d)) -> (e,d) :: apply_to_nf rules e

let showRule (Rule (e1,e2)) = showExpr e1 ^ " = " ^ showExpr e2

let rules = ref []

let add_file filename =
    let chan = open_in filename in
    try
        while true; do
        rules := parseRule (input_line chan) :: !rules
        done
    with End_of_file ->
        close_in chan