open TestSimple;;

open Printf;;
open Zil.Lambda;;
open Zil.Parse;;
open Zil;;

plan 9;;
(******************************************************************************)
(* Define library *)

let sym_lib = Library.read_from_file "src/library.tm";;
let sym_def = Library.get_lib_def sym_lib;;
let sym_sig = Library.get_lib_sig sym_lib;;

(******************************************************************************)
(* Syntax sugar *)

(* Convert i to (succ^i zero) *)
let rec number_to_nat n = match n with
  | 0 -> "zero"
  | 1 -> "succ zero"
  | n -> sprintf "succ (%s)" (number_to_nat (n-1))
	
(* Convert [a;b;c] to con A (f a) (con A (f b) (con A (f c) (nil A))) *)
let rec list_to_list a f xs = match xs with
  | [] -> sprintf "nil %s" a
  | x::xs -> sprintf "con %s %s (%s)" a (f x) (list_to_list a f xs)

(* Convert [1;2;3] to a list of nat *)
let list_to_natlist = list_to_list "Nat"
  (fun x -> (match x with 0 -> number_to_nat 0 | x -> sprintf "(%s)" (number_to_nat x)))


(* Generate a free_def from a list of term strings and a list of type strings *)
let instantiate_free (mm, aa) = {
  term_info = (fun i ->
    if i < List.length mm
    then Some (eval ~sym_def:sym_def (parse_term (List.nth mm i)))
    else None);
  type_info = (fun i ->
    if i < List.length aa
    then Some (parse_type (List.nth aa i))
    else None)
};;

(******************************************************************************)
(* Print functions for debugging *)

let print_free_lib lib =
  print_string
    (Library.to_string
      (fun i -> Term.Free((), i))
      (fun i -> Type.Free i)
      lib)

let print_sym_lib lib =
  print_string
    (Library.to_string
      (fun i -> Term.Sym((), i))
      (fun i -> Type.Sym(i, []))
      lib)

let print_hol_lib lib =
  print_string
    (Library.to_string
      (fun i -> Term.Hol((), i))
      (fun i -> Type.Hol i)
      lib)

(******************************************************************************)

let test_eval =
  let got = eval ~sym_def:sym_def (parse_term (sprintf "foldl Nat Nat add zero (%s)" (list_to_natlist [1;2;3]))) in
  is (Term.to_string got) (number_to_nat 6) "foldl Nat Nat add 0 [1;2;3] = 6";;

let test_eval =
  let got = eval ~sym_def:sym_def (parse_term (sprintf "foldr Nat Nat add zero (%s)" (list_to_natlist [1;2;3]))) in
  is (Term.to_string got) (number_to_nat 6) "foldr Nat Nat Nat add 0 [1;2;3] = 6";;

let test_eval =
  let got = eval ~sym_def:sym_def (parse_term (sprintf
      "foldl (List Nat) Nat (flip Nat (List Nat) (List Nat) (con Nat)) (nil Nat) (%s)"
      (list_to_natlist [1;2;3]))) in 
  is (Term.to_string got) (list_to_natlist [3;2;1]) "rev [1;2;3] = [3;2;1]";;

let test_eval =
  let got = eval ~sym_def:sym_def (parse_term (sprintf
      "foldl Nat Nat (flip Nat Nat Nat add) zero (%s)"
      (list_to_natlist [1;2;3]))) in
  is (Term.to_string got) (number_to_nat 6) "foldl (flip add) 0 [1;2;3] = 6";;

let test_eval =
  let got = eval ~sym_def:sym_def (parse_term (sprintf
      "foldr Nat Nat (flip Nat Nat Nat add) zero (%s)"
      (list_to_natlist [1;2;3]))) in
  is (Term.to_string got) (number_to_nat 6) "foldr (flip add) 0 [1;2;3] = 6";;

let test_eval =
  let got = eval ~sym_def:sym_def (parse_term (sprintf
      "foldr Nat (List Nat) (con Nat) (nil Nat) (%s)"
      (list_to_natlist [1;2;3]))) in
  is (Term.to_string got) (list_to_natlist [1;2;3]) "foldr con [] [1;2;3] = [1;2;3]";;

let test_flip =
  let got = eval ~sym_def:sym_def (parse_term
      "flip Nat (List Nat) (List Nat) (con Nat) (nil Nat) zero") in
  is (Term.to_string got) (list_to_natlist [0]) "flip con [] 0";;

let test_flip =
  let got = eval ~sym_def:sym_def (parse_term
      "flip Nat Nat Nat add zero zero") in
  is (Term.to_string got) (number_to_nat 0) "flip add 0 0";;

let test_typechecking =
  let annotated = well ~sym_sig:sym_sig (parse_term (sprintf
      "foldl (List Nat) Nat (flip Nat (List Nat) (List Nat) (con Nat)) (nil Nat) (%s)"
      (list_to_natlist [1;2;3]))) in
  let a = Term.extract_label annotated in
  let got = (match a with
  | Some a -> Type.to_string a
  | None ->  "Unit") in
  is got "List Nat" "Typechecking rev [1;2;3]"
