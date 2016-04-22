exception Lexer_error of string

val token : Lexing.lexbuf -> Parser.token
