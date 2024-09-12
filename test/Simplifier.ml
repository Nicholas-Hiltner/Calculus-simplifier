open Simplifier

let _ = add_file "../data/rules.ddx"

let _ = List.map print_endline (List.map showRule !rules)

let test_sub = Substitution.empty

let () = Substitution.print_sub test_sub

(* x, y are different substitutions combined *)
let x_dif = Substitution.singleton "x" (Int 4)
let y_dif = Substitution.singleton "y" (Int 3)
let xy_dif = Substitution.combine_substitutions (Some x_dif) (Some y_dif)
let () = print_endline "Expected: x -> 4, y -> 3"
let () = Substitution.print_sub @@ Option.get xy_dif; print_endline ""

(* x, x are the same substitution combined *)
let x_same = Substitution.singleton "x" (Int 4)
let x_same2 = Substitution.singleton "x" (Int 4)
let xx2_same = Substitution.combine_substitutions (Some x_same) (Some x_same2)
let () = print_endline "Expected: x -> 4"
let () = Substitution.print_sub @@ Option.get xx2_same; print_endline ""

(* x, x are contradictory substitutions *)
let x_con = Substitution.singleton "x" (Int 4)
let x_con2 = Substitution.singleton "x" (Int 3)
let xx2_con = Substitution.combine_substitutions (Some x_con) (Some x_con2)
let () = print_endline "Expected: xx2_con = None"
let () = 
    match xx2_con with
    | None -> print_endline "`xx2_con` is `None`"; print_endline ""
    | Some _ -> Substitution.print_sub @@ Option.get xx2_con; print_endline ""

(* subsitute var with int *)
let replace_var = Substitution.singleton "x" (Int 3)
let (orig_var : string Simplifier__.Ast.expr) = (Var "x")
let () = print_endline "Expected: 3"
let () = printExpr (Substitution.substitute replace_var orig_var); print_endline ""

(* subsitute var with binop *)
let replace_binop = Substitution.singleton "x" (Binop (Add, Var "x", Var "y"))
let (orig_binop : string Simplifier__.Ast.expr) = (Var "x")
let () = print_endline "Expected: x+y"
let () = printExpr (Substitution.substitute replace_binop orig_binop); print_endline ""

(* substitute binop with int *)
let replace_bint = Substitution.singleton "x" (Int 3)
let (orig_bint : string Simplifier__.Ast.expr) = (Binop (Add, Var "x", Int 4))
let () = print_endline "Expected: 3+4"
let () = printExpr (Substitution.substitute replace_bint orig_bint); print_endline ""

(* substitute ddx with int *)
let replace_ddx = Substitution.singleton "x" (Var "y")
let (orig_ddx : string Simplifier__.Ast.expr) = (Ddx ("x", Binop (Mult, Int 2, Var "x")))
let () = print_endline "Expected: d/dy (2*y)"
let () = printExpr (Substitution.substitute replace_ddx orig_ddx); print_endline ""

(* substitute function with int *)
let replace_fun = Substitution.singleton "x" (Int 3)
let (orig_fun : string Simplifier__.Ast.expr) = Fun ("cos", [Binop (Add, Var "x", Int 90)])
let () = print_endline "Expected: cos(3+90)"
let () = printExpr (Substitution.substitute replace_fun orig_fun); print_endline ""

(* multiple substitutions in one *)
let sub_1 = Substitution.singleton "x" (Int 3)
let sub_2 = Substitution.singleton "y" (Int 5)
let replace_mult = Option.get @@ Substitution.combine_substitutions (Some sub_1) (Some sub_2)
let (orig_mult : string Simplifier__.Ast.expr) = Binop(Add, Binop(Mult, Var "x", Var "y"), Binop(Subt, Var "x", Var "y"))
let () = print_endline "Expected: (3*5)+(3-5)"
let () = printExpr (Substitution.substitute replace_mult orig_mult); print_endline ""

(* matching basic case *)
let (mat_pat : string Simplifier__.Ast.expr) = Var "x"
let (mat_term : string Simplifier__.Ast.expr) = Int 5
let result = Option.get @@ ApplyRuleM.matching mat_pat mat_term
let () = print_endline "Expected: x -> 5"
let () = Substitution.print_sub @@ result; print_endline ""

(* matching basic case fail *)
let (mat_pat : string Simplifier__.Ast.expr) = Binop (Add, Int 6, Int 7)
let (mat_term : string Simplifier__.Ast.expr) = Int 5
let result = ApplyRuleM.matching mat_pat mat_term
let () = print_endline "Expected: `result` is `None`"
let () = 
    match result with
    | None -> print_endline "`result` is `None`"; print_endline ""
    | Some _ -> Substitution.print_sub @@ Option.get result; print_endline ""

(* var within an expression can be matched *)
let (mat_pat : string Simplifier__.Ast.expr) = Binop (Add, Var "x", Int 7)
let (mat_term : string Simplifier__.Ast.expr) = Binop (Add, Int 6, Int 7)
let result = Option.get @@ ApplyRuleM.matching mat_pat mat_term
let () = print_endline "Expected: x -> 6"
let () = Substitution.print_sub @@ result; print_endline ""

(* var matches to an expression *)
let (mat_pat : string Simplifier__.Ast.expr) = Binop (Add, Var "x", Int 7)
let (mat_term : string Simplifier__.Ast.expr) = Binop (Add, Binop (Mult, Var "y", Int 3), Int 7)
let result = Option.get @@ ApplyRuleM.matching mat_pat mat_term
let () = print_endline "Expected: x -> y*3"
let () = Substitution.print_sub @@ result; print_endline ""

(* matching with a derivative *)
let (mat_pat : string Simplifier__.Ast.expr) = Ddx ("x", Var "y")
let (mat_term : string Simplifier__.Ast.expr) = Ddx ("z", Var "a")
let result = Option.get @@ ApplyRuleM.matching mat_pat mat_term
let () = print_endline "Expected: x -> z, y -> a"
let () = Substitution.print_sub @@ result; print_endline ""

(* matching with a function (and a little bit of tomfoolery) *)
let (mat_pat : string Simplifier__.Ast.expr) = Fun ("cos", [Var "x"])
let (mat_term : string Simplifier__.Ast.expr) = Fun ("sec", [Var "x"])
let result = ApplyRuleM.matching mat_pat mat_term
let () = print_endline "`result` is `None`"
let () = 
    match result with
    | None -> print_endline "`result` is `None`"; print_endline ""
    | Some _ -> Substitution.print_sub @@ Option.get result; print_endline ""

(* matching with a function *)
let (mat_pat : string Simplifier__.Ast.expr) = Fun ("cos", [Var "x"; Var "y"])
let (mat_term : string Simplifier__.Ast.expr) = Fun ("cos", [Binop (Mult, Int 2, Var "x"); Var "y"])
let result = Option.get @@ ApplyRuleM.matching mat_pat mat_term
let () = print_endline "Expected: x -> 2*x, y -> y"
let () = Substitution.print_sub @@ result; print_endline ""


let rec get_rule x rules =
    match rules with
    | [] -> None
    | h :: t ->
        if x = 0 then Some h
        else (get_rule (x - 1) t)


(* toplevel application of x + 0 = x *)
let top_rule = Option.get @@ get_rule 19 !rules
let (top_expr : string Simplifier__.Ast.expr) = Binop (Add, Var "x", Int 0)
let result = Option.get @@ ApplyRuleM.apply_rule_toplevel top_rule top_expr
let () = print_endline "Expected: x"
let () = printExpr result; print_endline ""

(* toplevel application of x + 0 = x with deeper tree *)
let top_rule = Option.get @@ get_rule 19 !rules
let (top_expr : string Simplifier__.Ast.expr) = Binop (Add, Binop (Mult, Var "x", Int 3), Int 0) (* (x * 3) + 0 *)
let result = Option.get @@ ApplyRuleM.apply_rule_toplevel top_rule top_expr
let () = print_endline "Expected: x * 3"
let () = printExpr result; print_endline ""

(* toplevel application of x + 0 = x applying seperately for subtree *)
let top_rule = Option.get @@ get_rule 19 !rules
let (top_expr : string Simplifier__.Ast.expr) = Binop (Add, Binop (Add, Var "x", Int 0), Int 0)
let result_intermediate = Option.get @@ ApplyRuleM.apply_rule_toplevel top_rule top_expr
let result =              Option.get @@ ApplyRuleM.apply_rule_toplevel top_rule result_intermediate
let () = print_endline "Expected: x"
let () = printExpr result; print_endline ""

(* toplevel application with wrong operation *)
let top_rule = Option.get @@ get_rule 19 !rules
let (top_expr : string Simplifier__.Ast.expr) = Binop (Mult, Var "x", Int 0)
let result = ApplyRuleM.apply_rule_toplevel top_rule top_expr
let () = print_endline "Expected: `result` is `None`"
let () = 
    match result with
    | None -> print_endline "`result` is `None`"; print_endline ""
    | Some _ -> printExpr @@ Option.get result; print_endline ""

(* toplevel application with wrong integer value *)
let top_rule = Option.get @@ get_rule 17 !rules
let (top_expr : string Simplifier__.Ast.expr) = Binop (Mult, Var "x", Int 0)
let result = ApplyRuleM.apply_rule_toplevel top_rule top_expr
let () = print_endline "Expected: `result` is `None`"
let () = 
    match result with
    | None -> print_endline "`result` is `None`"; print_endline ""
    | Some _ -> printExpr @@ Option.get result; print_endline ""

(* toplevel application of d/dx x = 1 *)
let top_rule = Option.get @@ get_rule 8 !rules
let (top_expr : string Simplifier__.Ast.expr) = Ddx ("y", Var "y")
let result = Option.get @@ ApplyRuleM.apply_rule_toplevel top_rule top_expr
let () = print_endline "Expected: 1"
let () = printExpr result; print_endline ""

(* toplevel application of d/dx x = 1 with non-matching variables *)
let top_rule = Option.get @@ get_rule 8 !rules
let (top_expr : string Simplifier__.Ast.expr) = Ddx ("x", Var "y")
let result = ApplyRuleM.apply_rule_toplevel top_rule top_expr
let () = print_endline "Expected: `result` is `None`"
let () = 
    match result with
    | None -> print_endline "`result` is `None`"; print_endline ""
    | Some _ -> printExpr @@ Option.get result; print_endline ""

(* toplevel application of d/dx c = 0 *)
let top_rule = Option.get @@ get_rule 3 !rules
let (top_expr : string Simplifier__.Ast.expr) = Ddx("x", Int 3)
let result = Option.get @@ ApplyRuleM.apply_rule_toplevel top_rule top_expr
let () = print_endline "Expected: 0"
let () = printExpr result; print_endline ""

(* toplevel application of d/dx c = 0 on a constant expression that is non-integer *)
let top_rule = Option.get @@ get_rule 3 !rules
let (top_expr : string Simplifier__.Ast.expr) = Ddx("x", Binop (Add, Int 4, Int 3))
let result = Option.get @@ ApplyRuleM.apply_rule_toplevel top_rule top_expr
let () = print_endline "Expected: 0"
let () = printExpr result; print_endline ""

(* toplevel application of d/dx c = 0 on wrong type*)
let top_rule = Option.get @@ get_rule 3 !rules
let (top_expr : string Simplifier__.Ast.expr) = Ddx("x", Var "x")
let result = ApplyRuleM.apply_rule_toplevel top_rule top_expr
let () = print_endline "Expected: `result` is `None`"
let () = 
    match result with
    | None -> print_endline "`result` is `None`"; print_endline ""
    | Some _ -> printExpr @@ Option.get result; print_endline ""

(* toplevel application of d/dx c^n *)
let top_rule = Option.get @@ get_rule 2 !rules
let (top_expr : string Simplifier__.Ast.expr) = Ddx("x", Binop(Pow, Int 3, Binop(Add, Var "x", Int 5)))
let result = Option.get @@ ApplyRuleM.apply_rule_toplevel top_rule top_expr
let () = print_endline "Expected: (log(3) * (3^(x + 5)))*(d/dx (x + 5))"
let () = printExpr result; print_endline ""

(* toplevel application of d/dx c^n with non-constant base *)
let top_rule = Option.get @@ get_rule 2 !rules
let (top_expr : string Simplifier__.Ast.expr) = Ddx("x", Binop(Pow, Var "x", Binop(Add, Var "x", Int 5)))
let result = ApplyRuleM.apply_rule_toplevel top_rule top_expr
let () = print_endline "Expected: `result` is `None`"
let () = 
    match result with
    | None -> print_endline "`result` is `None`"; print_endline ""
    | Some _ -> printExpr @@ Option.get result; print_endline ""

(* application of d/dx c = 0 *)
let top_rule = Option.get @@ get_rule 3 !rules
let (top_expr : string Simplifier__.Ast.expr) = Ddx("x", Int 3)
let result = Option.get @@ ApplyRuleM.apply_rule top_rule top_expr
let () = print_endline "Expected: 0"
let () = printExpr result; print_endline ""

(* applying "x + 0 = 0" to (x + 0) + 1 (nested) *)
let top_rule = Option.get @@ get_rule 19 !rules
let (top_expr : string Simplifier__.Ast.expr) = Binop (Add, Binop (Add, Var "x", Int 0), Int 1)
let result = Option.get @@ ApplyRuleM.apply_rule top_rule top_expr
let () = print_endline "Expected: x + 1"
let () = printExpr result; print_endline ""

(* apply_rule on a non-integer constant *)
let top_rule = Option.get @@ get_rule 3 !rules
let (top_expr : string Simplifier__.Ast.expr) = Ddx("x", Binop (Add, Int 4, Int 3))
let result = Option.get @@ ApplyRuleM.apply_rule top_rule top_expr
let () = print_endline "Expected: 0"
let () = printExpr result; print_endline ""

(* application of d/dx x = 1 with non-matching variables *)
let top_rule = Option.get @@ get_rule 8 !rules
let (top_expr : string Simplifier__.Ast.expr) = Ddx ("x", Var "y")
let result = ApplyRuleM.apply_rule top_rule top_expr
let () = print_endline "Expected: `result` is `None`"
let () = 
    match result with
    | None -> print_endline "`result` is `None`"; print_endline ""
    | Some _ -> printExpr @@ Option.get result; print_endline ""

(* apply_rule only applies the rule the first opportunity to do so *)
let top_rule = Option.get @@ get_rule 17 !rules
let (top_expr : string Simplifier__.Ast.expr) = 
    Binop (
        Mult,
        Binop (Mult, Binop (Mult, Var "x", Int 1), Binop (Mult, Var "x", Int 1)),
        Binop (Mult, Binop (Mult, Var "x", Int 1), Binop (Mult, Var "x", Int 1))
    )
let result = Option.get @@ ApplyRuleM.apply_rule top_rule top_expr
let () = print_endline "Expected: (x*(x*1))*((x*1)*(x*1))"
let () = printExpr result; print_endline ""

(* taking derivatives on a variable not being differentiated upon should not work *)
let top_rule = Option.get @@ get_rule 3 !rules
let (top_expr : string Simplifier__.Ast.expr) = Ddx ("x", Var "y")
let result = ApplyRuleM.apply_rule top_rule top_expr
let () = print_endline "Expected: `result` is `None`"
let () = 
    match result with
    | None -> print_endline "`result` is `None`"; print_endline ""
    | Some _ -> printExpr @@ Option.get result; print_endline ""