open Printf
open Lambda
open Parse


(* Auxiliary functions *)

let def name impl =
  Term.BuiltinFun ((), impl, Some (Term.Sym ((), name)))

let def2 name impl =
  let f m1 = Term.BuiltinFun ((), impl m1, Some (Term.App ((), Term.Sym ((), name), m1))) in
  def name f

let def3 name impl =
  let f m1 m2 = Term.BuiltinFun ((), impl m1 m2, Some
    (Term.App ((),
      (Term.App ((),
        Term.Sym ((), name),
        m1)),
      m2))) in
  def2 name f

let def_int_unop name op =
  let f x = match x with
    | Term.Int (_, i) -> Term.Int ((), op i)
    | _ -> parse_term (sprintf "%s (%s)" name (Term.to_string x)) in
  (name, def name f, parse_type "Int -> Int")

let def_int_binop name op =
  let f x y = match (x, y) with
    | (Term.Int (_, i), Term.Int (_, j)) -> Term.Int ((), op i j)
    | (_, _) -> parse_term (sprintf "%s (%s) (%s)" name (Term.to_string x) (Term.to_string y)) in
  (name, def2 name f, parse_type "Int -> Int -> Int")


(* Definitions of built-in functions *)

let zero = ("b_zero", Term.Int ((), 0), parse_type "Int")
let succ = def_int_unop "b_succ" (fun x -> x + 1)

let add = def_int_binop "b_add" (+)
let sub = def_int_binop "b_sub" (-)
let mul = def_int_binop "b_mul" (fun x y -> x * y)
let div = def_int_binop "b_div" (fun x y -> x / y)
let max = def_int_binop "b_max" max

let foldNat =
  let name = "b_foldNat" in
  let impl a m_f m_init m_i =
    match m_i with
    | Term.Int (_, i) when i <= 0 -> m_init
    | Term.Int (_, i) when i > 0 -> parse_term (sprintf
      "(%s) (%s (%s) (%s) (%s) (%s))"
      (Term.to_string m_f)
      name
      (Type.to_string a)
      (Term.to_string m_f)
      (Term.to_string m_init)
      (Term.to_string (Term.Int ((), i-1))))
    | _ -> parse_term (sprintf
      "%s (%s) (%s) (%s) (%s)"
      name
      (Type.to_string a)
      (Term.to_string m_f)
      (Term.to_string m_init)
      (Term.to_string m_i)) in
  
  let m = Term.FUN ((), def3 name (impl (Type.Var 0)), empty_env, Some (Term.Sym ((), name))) in
  (name, m, parse_type "@ (#0 -> #0) -> #0 -> Int -> #0")

let foldNatNat =
  let name = "b_foldNatNat" in
  let impl a m_f m_init m_i =
    match m_i with
    | Term.Int (_, i) when i <= 0 -> m_init
    | Term.Int (_, i) when i > 0 -> parse_term (sprintf
      "(%s) %d (%s (%s) (%s) (%s) %d)"
      (Term.to_string m_f)
      i
      name
      (Type.to_string a)
      (Term.to_string m_f)
      (Term.to_string m_init)
      (i-1))
    | _ -> parse_term (sprintf
      "%s (%s) (%s) (%s) (%s)"
      name
      (Type.to_string a)
      (Term.to_string m_f)
      (Term.to_string m_init)
      (Term.to_string m_i)) in
  
  let m = Term.FUN ((), def3 name (impl (Type.Var 0)), empty_env, Some (Term.Sym ((), name))) in
  (name, m, parse_type "@ (Int -> #0 -> #0) -> #0 -> Int -> #0")


