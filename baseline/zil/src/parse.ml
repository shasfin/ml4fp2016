
let parse_type s = Parser.parse_type Lexer.token (Lexing.from_string s)

let parse_term s = Parser.parse_term Lexer.token (Lexing.from_string s)


let example = "* * { [#1 -> #0] [List #1] : $0 (nil #0) { [#1] [List #1] : con #0 ($3 $1) (map #1 #0 $3 $0) } }"
