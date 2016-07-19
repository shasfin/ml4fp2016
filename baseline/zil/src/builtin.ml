open Printf
open Lambda
open Parse


(* Auxiliary functions *)

let def name impl =
  Term.BuiltinFun ((), impl, Some (Term.Sym ((), name)))

(* impl has the type unit Term.t -> unit Term.t *)
let def1_ignore name impl =
  def name (fun (lib, m) -> impl m)

(* impl has the type unit Term.t -> unit Term.t -> unit Term.t *)
let def2_ignore name impl =
  let f1 m1 (_, m2) = impl m1 m2 in
  let f2 m1 = Term.BuiltinFun ((), f1 m1, Some (Term.App ((), Term.Sym ((), name), m1))) in
  def1_ignore name f2

(* impl has the type unit Term.t -> unit Term.t -> sym_def -> unit Term.t *)
let def2 name impl =
  let f1 m1 (lib, m2) = impl m1 m2 lib in
  let f2 m1 = Term.BuiltinFun ((), f1 m1, Some (Term.App ((), Term.Sym ((), name), m1))) in
  def1_ignore name f2

(* impl has the type unit Term.t -> unit Term.t -> unit Term.t -> unit Term.t *)
let def3_ignore name impl =
  let f1 m1 m2 (_, m3) = impl m1 m2 m3 in
  let f2 m1 m2 = Term.BuiltinFun ((), f1 m1 m2, Some
    (Term.App ((),
      (Term.App ((),
        Term.Sym ((), name),
        m1)),
      m2))) in
  def2_ignore name f2

(* impl has the type unit Term.t -> unit Term.t -> unit Term.t -> sym_def -> unit Term.t *)
let def3 name impl =
  let f1 m1 m2 (lib, m3) = impl m1 m2 m3 lib in
  let f2 m1 m2 = Term.BuiltinFun ((), f1 m1 m2, Some
    (Term.App ((),
      (Term.App ((),
        Term.Sym ((), name),
        m1)),
      m2))) in
  def2_ignore name f2


(* op : int -> int *)
let def_int_unop name op =
  let f x = match x with
    | Term.Int (_, i) -> Term.Int ((), op i)
    | Term.APP (_, Term.Sym (_, "undefined"), _) -> raise (Undefined (sprintf
      "Problem evaluating %s. Undefined argument"
      name))
    | _ -> invalid_arg "Please reduce before evaluation" in
  (name, def1_ignore name f, parse_type "Int -> Int")

(* op : int -> int -> int *)
let def_int_binop name op =
  let f x y = match (x, y) with
    | (Term.Int (_, i), Term.Int (_, j)) -> Term.Int ((), op i j)
    | (Term.APP (_, Term.Sym (_, "undefined"), _), _) -> raise (Undefined (sprintf
      "Problem evaluating %s. Undefined argument"
      name))
    | (_, Term.APP (_, Term.Sym (_, "undefined"), _)) -> raise (Undefined (sprintf
      "Problem evaluating %s. Undefined argument"
      name))
    | (_, _) -> invalid_arg "Please reduce before evaluation" in
  (name, def2_ignore name f, parse_type "Int -> Int -> Int")


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
  let impl a m_f m_init m_i lib =
    let rec impl_aux acc m_i =
      match m_i with
      | Term.Int (_, i) when i <= 0 -> acc
      | Term.Int (_, i) ->
        impl_aux
          (eval ~sym_def:lib
            (Term.App ((),
              m_f,
              acc)))
          (Term.Int ((), i-1))
      | Term.APP (_, Term.Sym (_, "undefined"), _) -> raise (Undefined (sprintf
        "Problem evaluating %s (%s) (%s) (%s). Please reduce %s before evaluation."
        name
        (Term.to_string m_f)
        (Term.to_string m_init)
        (Term.to_string m_i)
        (Term.to_string m_i)))
      | _ -> invalid_arg "Please reduce before evaluation" in

  impl_aux m_init m_i in

  let m = Term.FUN ((), def3 (name^"_b") (impl (Type.Var 0)), empty_env, Some (Term.Sym ((), name))) in
  (name, m, parse_type "@ (#0 -> #0) -> #0 -> Int -> #0")


let foldNatNat =
  let name = "b_foldNatNat" in
  let impl a m_f m_init m_i lib =
    let rec impl_aux acc m_i =
      match m_i with
      | Term.Int (_, i) when i <= 0 -> acc
      | Term.Int (_, i) when i > 0 ->
        impl_aux
          (eval ~sym_def:lib
            (Term.App ((),
              (Term.App ((),
                m_f,
                m_i)),
              acc)))
          (Term.Int ((), i-1))
      | Term.APP (_, Term.Sym (_, "undefined"), _) -> raise (Undefined (sprintf
        "Problem evaluating %s (%s) (%s) (%s). Please reduce %s before evaluation."
        name
        (Term.to_string m_f)
        (Term.to_string m_init)
        (Term.to_string m_i)
        (Term.to_string m_i)))
      | _ -> invalid_arg "Please reduce before evaluation" in

    impl_aux m_init m_i in
  
  let m = Term.FUN ((), def3 name (impl (Type.Var 0)), empty_env, Some (Term.Sym ((), name))) in
  (name, m, parse_type "@ (Int -> #0 -> #0) -> #0 -> Int -> #0")

let filter_aux =
  let name = "b_filter_aux" in
  let impl a m_f m_x m_xs lib =
    match Term.to_string (eval ~sym_def:lib (Term.App ((), m_f, m_x))) with
    | "true" -> eval ~sym_def:lib (parse_term (sprintf
        "con (%s) (%s) (filter (%s) (%s) (%s))"
        (Type.to_string a)
        (Term.to_string m_x)
        (Type.to_string a)
        (Term.to_string m_f)
        (Term.to_string m_xs)))
    | "false" -> eval ~sym_def:lib (parse_term (sprintf
        "filter (%s) (%s) (%s)"
        (Type.to_string a)
        (Term.to_string m_f)
        (Term.to_string m_xs)))
    | x -> invalid_arg "Please reduce before evaluation" in
  
  let m = Term.FUN ((), def3 name (impl (Type.Var 0)), empty_env, Some (Term.Sym ((), name))) in
  (name, m, parse_type "@ (#0 -> Bool) -> #0 -> List #0 -> List #0")


let is_zero =
  let name = "b_is_zero" in
  let impl m_i =
    match m_i with
    | Term.Int (_, 0) -> Term.Sym ((), "true")
    | Term.Int _ -> Term.Sym ((), "false")
    | _ -> invalid_arg "Please reduce before evaluation" in

  (name, def1_ignore name impl, parse_type "Int -> Bool")

