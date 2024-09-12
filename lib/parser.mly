%{
open Ast
%}

%token <int> INT
%token <string> VAR
%token <string> DDX
%token TIMES  
%token PLUS
%token MINUS
%token DIV
%token POW
%token LPAREN
%token RPAREN
%token EQUALS
%token COMMA
%token EOF

/* Order in which these are written determines the precedence */
%nonassoc DDX
%left PLUS MINUS
%left TIMES DIV
%nonassoc POW

%start <string Ast.expr> prog
%start <string Ast.rule> rule

%%

prog:
	| e = expr; EOF { e }
	;

exprList:
	| x = expr; COMMA; xs = exprList {x :: xs}
	| x = expr { [x] }
	;
	
expr:
	| x = VAR { Var x }
	| x = INT { Int x }
    | x = VAR; LPAREN; xs = exprList; RPAREN { Fun (x, xs) }
	| e1 = expr; POW; e2 = expr { Binop (Pow, e1, e2) } 
	| e1 = expr; TIMES; e2 = expr { Binop (Mult, e1, e2) } 
	| e1 = expr; DIV; e2 = expr { Binop (Div, e1, e2) } 
	| e1 = expr; PLUS; e2 = expr { Binop (Add, e1, e2) }
	| e1 = expr; MINUS; e2 = expr { Binop (Subt, e1, e2) }
	| LPAREN; e=expr; RPAREN {e} 
	| x = DDX; e=expr { Ddx (x, e) }
	| MINUS; e = expr { Fun ("-", [e]) }
	;

rule:
	| e1=expr;EQUALS;e2=expr;EOF { Rule (e1,e2)}