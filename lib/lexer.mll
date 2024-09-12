{
    open Parser
}

let white = [' ' '\t' '\r' '\n']+
let digit = ['0'-'9']
let int = '-'? digit+
let letter = ['a'-'z' 'A'-'Z']
let id = '\\'? letter+

rule read = 
    parse
    | white { read lexbuf }
    | "*" { TIMES }
    | "+" { PLUS }
    | "/" { DIV }
    | "-" { MINUS }
    | "^" { POW }
    | "(" { LPAREN }
    | ")" { RPAREN }
    | "," { COMMA }
    | "=" { EQUALS }
    | "d/d" (id as letr) { DDX letr }
    | id { VAR (Lexing.lexeme lexbuf) }
    | int { INT (int_of_string (Lexing.lexeme lexbuf)) }
    | eof { EOF }