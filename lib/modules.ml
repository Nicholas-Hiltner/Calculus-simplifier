open Ast

module type Substitution = sig

    type 'a substitution

(** Singleton [x] [e] returns a substitution that maps [x] to [e]. *)
    val singleton : string -> 'a expr -> 'a substitution

(** empty returns a substitution that maps nothing. *)
    val empty : 'a substitution

(** for_all allows you to check whether a substitution satisfies a predicate.
    It returns true if the predicate is true for all variables in the substitution.
    This can be used to check if constant-variables are mapped to constants, for example. *)
    val for_all : (string -> 'a expr -> bool) -> 'a substitution -> bool

(** combine_substitutions [subst1] [subst2]
    compares the composition of the substitutions [subst1] and [subst2] for compatibility:
    equal variables need to be mapped to the same thing.
    If the composition is compatible, it returns the composition. *)
    val combine_substitutions : 'a substitution option -> 'a substitution option -> 'a substitution option
    exception MalformedSubstitution of string

(** substitute [subst] [pat] replaces the variables in [pat] by
    whatever the subtitution [subst] tells them to be.
    If a variable occurs in [pat] that is not in [subst], a NotFound error is raised.
    An occurrence in 'ddx' requires the variable to be a single variable.
    If it is given an expression instead, the MalformedSubstitution error is raised. *)
    val substitute : 'a substitution -> string expr -> 'a expr

end

module type ApplyRule = sig
(** apply_rule [rule] [expr] tries to apply the rule [rule] to the expression [expr].
    If succesful, it returns the rewritten form of [expr], and it returns None otherwise.
    The function apply_some_rule does the same on lists of expressions,
    it applies the rule to precisely one element (if possible). *)
    val apply_rule : string rule -> string expr -> string expr option
    (* val matching *)
end

(** no_vars [e] returns whether there are any variables in [e].
    The purpose of this function is to know if the subexpression
    can be considered to be a constant, i.e. for a rule like 'd/dx c = 0'.
    For that reason, the occurrence of d/dx itself is not considered a variable. *)
    let rec no_vars e =
        match e with
        | Var x -> (
            if String.get x 0 = 'c' then true
            else false
        )
        | Int _ -> true
        | Binop (_, l, r) -> (no_vars l) && (no_vars r)
        | Ddx (_, e) -> no_vars e
        | Fun (_, lst) -> List.fold_left (fun acc e -> acc && no_vars e) true lst

module ApplyRule (Substitution : Substitution) = struct
(** matching [pattern] [term]
    finds a substitution that can be applied to [pattern] to make
    it equal [term], if such a substitution exists.
    Otherwise, it returns None.
    
    [matching a b = Some s] ==> [substitute s a = b]
    (Exists s2. [matching a b = Some s2]) <=> [substitute s a = b] *)
    let rec matching patt term =
        match (patt, term) with
        | (Int _, Int _) -> Some Substitution.empty
        | (Binop (op, l1, r1), Binop (op', l2, r2)) ->
            if op <> op' then None
            else Substitution.combine_substitutions (matching l1 l2) (matching r1 r2)
        | (Ddx (v1, e1), Ddx (v2, e2)) ->
            Substitution.combine_substitutions (Some (Substitution.singleton v1 (Var v2))) (matching e1 e2)
        | (Fun (f, lst1), Fun (f', lst2)) -> 
            if f <> f' then None
            else (
                match 
                    (* tests if the expressions are of the same structure. `None` is the result if not.*)
                    (List.fold_left2
                    (fun acc a b -> match acc with | None -> None | Some _ -> matching a b) 
                    (Some Substitution.empty) lst1 lst2) with
                | None -> None
                | _ ->
                    List.fold_left 
                    (fun acc n -> Substitution.combine_substitutions acc n)
                    (Some Substitution.empty)
                    (List.map2 (fun a b -> matching a b) lst1 lst2)
            )
        | (Var x, _) ->
            if no_vars patt && not (no_vars term) then None
            else Some (Substitution.singleton x term) (*(Substitution.singleton x term)*)
        | _ -> None



(** apply_rule_toplevel [rule] [expr]
    tries to apply the rule [rule] to the expression,
    returning the rewritten form if the rule can be applied to the expression as is.
    This function does not try to apply the rule to any subexpressions *)
    let apply_rule_toplevel (Rule (lhs,rhs) : string rule) (expr : string expr) =
        let is_compatible x y = (
            match (x, y) with
            | (Int x', Int y') -> x' = y'
            | (Var _, _) -> true
            | (Int _, Var _) -> false
            | _ -> false
        )
        in
        match (lhs, expr) with
        | (Binop (op, l, r), Binop (op', l', r')) ->
            if op <> op' then None
            else if not (is_compatible r r') then None
            else if not (is_compatible l l') then None
            else Some (Substitution.substitute (Option.get (matching lhs expr)) rhs)
        | (Ddx (x, e), Ddx (x', e')) -> (
            match (e, e') with
            | (Var v, Var v') ->
                if ((x = v && x' = v') || (x <> v && x' <> v')) && (not @@ no_vars e)
                    then Some (Substitution.substitute (Option.get (matching lhs expr)) rhs)
                else None
            | (Binop (op, l, _), Binop (op', l', _)) ->
                if op <> op' then None
                else if op = Pow && (no_vars l && not (no_vars l')) then None
                else Some (Substitution.substitute (Option.get (matching lhs expr)) rhs)
            (* constants *)
            | _ -> 
                if no_vars e && no_vars e' 
                then Some (Substitution.substitute (Option.get (matching lhs expr)) rhs)
                else None
        )
        | _ -> None

(** This is the main work-horse. *)
    let rec apply_rule (rl: string rule) (expr: string expr) : string expr option =
        match expr with
        | Var _ -> apply_rule_toplevel rl expr
        | Int _ -> apply_rule_toplevel rl expr
        | Binop (op, l, r) -> (
            match apply_rule_toplevel rl expr with
            | Some x -> Some x
            | None -> (
                match apply_rule rl l with
                | Some x -> Some (Binop (op, x, r))
                | None -> (
                    match apply_rule rl r with
                    | Some x -> Some (Binop (op, l, x))
                    | None -> None
                )
            )
        )
        | Fun _ -> None (* there are no function rules... *)
        | Ddx _ -> apply_rule_toplevel rl expr
end  