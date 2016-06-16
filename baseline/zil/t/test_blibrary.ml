open TestSimple;;
open Printf;;
open Core.Std;;

open Zil.Lambda;;
open Zil.Parse;;
open Zil;;

plan 14;;

(******************************************************************************)
(* Define library *)

let sym_lib = Library.read_from_file "src/b_library.tm";;
let sym_def = Library.get_lib_def sym_lib;;

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
  | x::xs -> sprintf "con %s (%s) (%s)" a (f x) (list_to_list a f xs)

(* Convert [1;2;3] to a list of nat *)
let list_to_natlist = list_to_list "Nat" number_to_nat

(* Convert [1;2;3] to a list of int *)
let list_to_intlist = list_to_list "Int" string_of_int

(* Convert "Nat" "List Nat" ("succ...","con...") to pair Nat (List Nat) (succ...) (con...) *)
let pair_to_pair a b (m, n) = sprintf "pair (%s) (%s) (%s) (%s)" a b m n


(* Generate a free_def from a list of term strings and a list of type strings *)
let instantiate_free (mm, aa) = {
  term_info = (fun i ->
    if i < List.length mm
    then Some (eval ~sym_def:sym_def (parse_term (List.nth_exn mm i)))
    else None);
  type_info = (fun i ->
    if i < List.length aa
    then Some (parse_type (List.nth_exn aa i))
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
(* Test some of the library functions *)


(*(* test addition *)
let test_add n m msg =
  let got = eval ~debug:true ~sym_def:sym_def (parse_term (sprintf "b_add (%s) (%s)" (string_of_int n) (string_of_int m))) in
  is (Term.to_string got) (string_of_int (n+m)) msg

let test_add_0_0 = test_add 0 0 "0+0";;
let test_add_1_0 = test_add 1 0 "1+0";;
let test_add_0_1 = test_add 0 1 "0+1";;
let test_add_3_5 = test_add 1 1 "1+1";;
let test_add_2_3 = test_add 2 3 "2+3";;*)


let test input output msg =
  let got = eval ~debug:true ~sym_def:sym_def (parse_term input) in
  is (Term.to_string got) output msg


let test_replicate =
  let rec replicate n x = (match n with
    | 0 -> []
    | n when n > 0 -> x :: (replicate (n-1) x)
    | _ -> invalid_arg "The first argument to replicate must be positive") in
    
  let n = 3 in
  let x = [] in

  test
    (sprintf "replicate (List Int) (%s) (%s)"
      (string_of_int n)
      (list_to_intlist x))
    (list_to_list "(List Int)" list_to_intlist (replicate n x))
    "test replicate"


