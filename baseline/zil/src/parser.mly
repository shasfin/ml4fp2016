%{

open Lambda

%}

%token <string> TYPE_SYM
%token <string> TERM_SYM
%token <int>    TYPE_VAR
%token <int>    TERM_VAR
%token <int>    TYPE_HOL
%token <int>    TERM_HOL
%token          TYPE_ARR
%token          TYPE_ALL
%token          TERM_ABS
%token LPAREN RPAREN
%token LBRACK RBRACK
%token LBRACE RBRACE
%token PARSEP
%token EOI

%type <     Lambda.Type.t> parse_type
%type <unit Lambda.Term.t> parse_term

%start parse_type parse_term

%nonassoc TYPE_ALL
%right    TYPE_ARR


%%
parse_type:
  | a = type_ EOI
  { a }

type_:
  | i = TYPE_SYM l = type_arg*
  { Type.Sym (i, l) }

  | i = TYPE_VAR
  { Type.Var i }

  | i = TYPE_HOL
  { Type.Hol i }

  | a = type_ TYPE_ARR b = type_
  { Type.Arr (a, b) }

  | TYPE_ALL a = type_
  { Type.All a }

  | LPAREN a = type_ RPAREN
  { a }

type_arg:
  | i = TYPE_SYM
  { Type.Sym (i, []) }

  | i = TYPE_VAR
  { Type.Var i }

  | i = TYPE_HOL
  { Type.Hol i }

  | LPAREN a = type_ RPAREN
  { a }


parse_term:
  | m = term EOI
  { m }

term:
  | m = term_cal
  { m }

  | TERM_ABS m = term
  { Term.ABS ((), m) }

term_cal:
  | m = term_arg
  { m }

  | m = term_cal n = term_arg
  { Term.App ((), m, n) }

  | m = term_cal a = type_arg
  { Term.APP ((), m, a) }

term_arg:
  | i = TERM_SYM
  { Term.Sym ((), i) }

  | i = TERM_VAR
  { Term.Var ((), i) }

  | i = TERM_HOL
  { Term.Hol ((), i) }

  | LBRACE l = term_par+ PARSEP m = term RBRACE 
  { List.fold_right (fun a m -> Term.Abs ((), a, m)) l m }

  | LPAREN m = term RPAREN
  { m }

term_par:
  | LBRACK a = type_ RBRACK
  { a }