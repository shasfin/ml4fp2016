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
  let got = eval ~debug:false ~sym_def:sym_def (parse_term input) in
  is (Term.to_string got) (Term.to_string (parse_term output)) msg

(*let test_foldNat =
  let n = 1 in
  let m = 7 in
  test
    (sprintf "b_foldNat Int (b_mul %d) 1 %d" m n)
    (string_of_int (int_of_float ((float_of_int m) ** (float_of_int n))))
    (sprintf "%d ^ %d" m n)*)

let test_unknown =
  let n = 2 in
  let m = 7 in
  test
    (sprintf "(b_foldNat Int (b_foldNat Int (b_mul %d) 1) 1 %d)"
      m n)
    "boh"
    (sprintf "unknown %d" n)

(*let test_overflow =
  test
    "b_foldNat Int (b_mul 7) 1 823543"
    "boh"
    "b_foldNat_b (b_mul 7) 1 823543"*)

(*let rec add x = match x with
  | n when n <= 0 -> 0
  | n -> n + (add (n - 1))*)

(*let rec add x = match x with
  | n when n <= 0 -> 0
  | n -> (add (n - 1)) + n*)

(*let add x =
   let rec add_aux a n = match n with
   | n when n <= 0 -> a
   | n -> add_aux (a + n) (n - 1) in
   add_aux 0 x

let test_overflow = add 823543;;*)

(*let test_foldNat_partial =
  let n = 3 in
  let xs = [1;2] in
  test
    (sprintf "map Int Int (b_foldNat Int (b_mul %d) 1) (%s)"
      n
      (list_to_intlist xs))
    (list_to_intlist (List.map ~f:(fun x -> int_of_float ((float_of_int n)**(float_of_int x))) xs))
    "use foldNat as a partial function"*)

(*let test_foldNat_builtin =
  let n = 3 in
  let m = 5 in
  test
    (sprintf "b_mul %d (b_foldNat Int (b_mul %d) 1 %d)" n m m)
    (string_of_int (n * int_of_float ((float_of_int m) ** (float_of_int m))))
    "mul n (foldNat ...)"*)

(*let test_unknown =
  let n = 3 in
  test
    (sprintf "b_mul %d (b_foldNat Int (b_foldNat Int (b_mul %d) %d) %d %d)"
      n n n n n)
    "boh"
    (sprintf "unknown %d" n)*)

(*let test_factorial =
  let rec factorial n = match n with
  | 0 | 1 -> 1
  | n when n > 1 -> n * (factorial (n-1))
  | _ -> invalid_arg "Argument of factorial must be positive" in
  
  let n = 5 in
  test
    (sprintf "factorial %s" (string_of_int n))
    (string_of_int (factorial n))
    (sprintf "factorial %s" (string_of_int n))*)

(*let test_range =
  let n = 3 in
  let m = 5 in
  test
    (sprintf "enumFromTo %s %s"
      (string_of_int n)
      (string_of_int m))
    (list_to_intlist (List.range ~stop:`inclusive n m))
    (sprintf "enumFromTo %s %s"
      (string_of_int n)
      (string_of_int m))*)

(*let test_replicate =
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
    "test replicate"*)


