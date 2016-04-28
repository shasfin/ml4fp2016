{

open Lexing
open Parser

exception Lexer_error of string

let tail s = String.sub s 1 ((String.length s) - 1)

}

rule token = parse
  | [' ' '\n']
    { token lexbuf }
  
  | ['A'-'Z'] ['A'-'Z' 'a'-'z' '0'-'9' '_']* as tok
    { TYPE_SYM tok }
  | ['a'-'z'] ['A'-'Z' 'a'-'z' '0'-'9' '_']* as tok
    { TERM_SYM tok }
  
  | ['#'] ['0'-'9']+ as tok
    { TYPE_VAR (int_of_string (tail tok)) }
  | ['$'] ['0'-'9']+ as tok
    { TERM_VAR (int_of_string (tail tok)) }

  | ['^'] ['0'-'9']+ as tok
    { TYPE_HOL (int_of_string (tail tok)) }
  | ['?'] ['0'-'9']+ as tok
    { TERM_HOL (int_of_string (tail tok)) }

  | ['_'] ['0'-'9']+ as tok
    { TERM_FREE (int_of_string (tail tok)) }
  | ['&'] ['0'-'9']+ as tok
    { TYPE_FREE (int_of_string (tail tok)) }

  | "->"  { TYPE_ARR }
  | ['@'] { TYPE_ALL }
  | ['*'] { TERM_ABS }

  | ['('] { LPAREN }
  | [')'] { RPAREN }
  | ['['] { LBRACK }
  | [']'] { RBRACK }
  | ['{'] { LBRACE }
  | ['}'] { RBRACE }

  | [':'] { PARSEP }

  | eof
    { EOI }
  
  | _
    { raise (Lexer_error (Printf.sprintf "Unexpected character '%s' at position %d" (lexeme lexbuf) (lexeme_start lexbuf))) }
