open TestSimple;;

open Zil.Lambda;;
open Zil.Parse;;

plan 1;;

let empty_env = {
  Term.type_stack = [];
  Term.term_stack = [];
};;

(* Recursive list data-type *)
let list_sig = 1 (* one free parameter *)
let list_def = parse_type "@ #0 -> (#1 -> List #1 -> #0) -> #0";;

(* constructors *)
let list_nil_sig = parse_type "@ List #0";;
let list_nil_def = parse_term "* * { [#0] [#1 -> List #1 -> #0] : $1 }";;

let list_con_sig = parse_type "@ #0 -> List #0 -> List #0";;
let list_con_def = parse_term "* { [#0] [List #0] : * { [#0] [#1 -> List #1 -> #0] : $0 $3 $2 } }";;

(* functions *)
let list_map_sig = parse_type "@ @ (#1 -> #0) -> List #1 -> List #0";;
let list_map_def = parse_term "* * { [#1 -> #0] [List #1] : $0 #0 (nil #0) { [#1] [List #1] : con #0 ($3 $1) (map #1 #0 $3 $0) } }";;

(* Make the definitions usable by the evaluator *)
let list_nil_fun = name "nil" (eval list_nil_def);;
let list_con_fun = name "con" (eval list_con_def);;
let list_map_fun = name "map" (eval list_map_def);;

let sym_def_types = function
  | "List" -> Some list_def
  | _ -> None
;;

let sym_def_terms = function
  | "nil" -> Some list_nil_fun
  | "con" -> Some list_con_fun
  | "map" -> Some list_map_fun
  | _ -> None
;;

let sym_def = {
  type_info = sym_def_types;
  term_info = sym_def_terms;
};;

let sym_sig_types = function
    | "List" -> Some 1
    | _ -> None
;;

let sym_sig_terms = function
    | "nil" -> Some list_nil_sig
    | "con" -> Some list_con_sig
    | "map" -> Some list_map_sig
    | _ -> None
;;

let sym_sig = {
    type_info = sym_sig_types;
    term_info = sym_sig_terms;
};;

(***************************************************************************)
(* Testing evaluation *)

let got = eval ~sym_def:sym_def (parse_term "map A B f (con A x (con A y (con A z (nil A))))") in
is (Term.to_string got) "con B (f x) (con B (f y) (con B (f z) (nil B)))" "basic symbolic evaluation"


(****************************************************************************)
(* Testing substitution *)
let a = parse_type "@ (#1 -> #0) -> List #1 -> List #0";;
let b = parse_type "A";;
let i = 0;;
let got = Type.subst b i a in
is (Type.to_string got) "@ (A -> #0) -> List A -> List #0" "Map substitution"


(****************************************************************************)
(* Testing typechecking *)
let f_sig = parse_type "A -> B";;
let x_sig = parse_type "A";;
let y_sig = parse_type "A";;
let z_sig = parse_type "A";;

let sym_sig_types = function
    | "List" -> Some 1
    | "A" -> Some 0
    | "B" -> Some 0
    | _ -> None
;;

let sym_sig_terms = function
    | "nil" -> Some list_nil_sig
    | "con" -> Some list_con_sig
    | "map" -> Some list_map_sig
    | "f" -> Some f_sig
    | "x" -> Some x_sig
    | "y" -> Some y_sig
    | "z" -> Some z_sig
    | _ -> None
;;

let sym_sig = {
    type_info = sym_sig_types;
    term_info = sym_sig_terms;
};;

let test_typechecking program expected_type ?msg:(msg="Basic typechecking") =
    let option_type = Term.extract_label (well ~sym_sig:sym_sig program) in
    let got_type = match option_type with
        | Some a -> a
        | None -> raise (Invalid_argument "No type found") in
    is (Type.to_string got_type) expected_type msg

let test1 =
    let program = parse_term "map A" in
    let expected_type = "@ (A -> #0) -> List A -> List #0" in
    test_typechecking program expected_type ~msg:"Typing map A"

let test2 =
    let program = parse_term "map A B f (con A x (con A x (con A y (con A z (nil A)))))" in
    let expected_type = "List B" in
    test_typechecking program expected_type ~msg:"Basic typecheck"

let test3 =
    let program = parse_term "map A B" in
    let expected_type = "(A -> B) -> List A -> List B" in
    test_typechecking program expected_type ~msg:"Typing map A B"


