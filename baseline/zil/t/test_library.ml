open TestSimple;;
open Printf;;
open Core.Std;;

open Zil.Lambda;;
open Zil.Parse;;
open Zil;;

plan 14;;

(******************************************************************************)
(* Define library *)

let sym_lib = Library.read_from_file "src/library.tm";;
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

(*
(* test addition *)
let test_add n m msg =
  let got = eval ~sym_def:sym_def (parse_term (sprintf "add (%s) (%s)" (number_to_nat n) (number_to_nat m))) in
  is (Term.to_string got) (number_to_nat (n+m)) msg

let test_add_0_0 = test_add 0 0 "0+0";;
let test_add_1_0 = test_add 1 0 "1+0";;
let test_add_0_1 = test_add 0 1 "0+1";;
let test_add_3_5 = test_add 1 1 "1+1";;
let test_add_2_3 = test_add 2 3 "2+3";;

(* test sum *)
let test_sum xs msg =
  let got = eval ~sym_def:sym_def (parse_term (sprintf "sum (%s)" (list_to_list "Nat" number_to_nat xs))) in
  is (Term.to_string got) (number_to_nat (List.fold_left (+) 0 xs)) msg
  
let test_sum1 = test_sum [] "sum []";;
let test_sum2 = test_sum [2] "sum [2]";;
let test_sum3 = test_sum [1;2;3] "sum [1;2;3]";;
let test_sum4 = test_sum [2;3;5;1] "sum [2;3;5;1]";;

(* test foldr *)
(* to_term f :: Nat -> Nat -> Nat *)
let test_foldr_nat f init xs output msg =
  let got = eval ~sym_def:sym_def (parse_term (sprintf "foldr Nat Nat (%s) (%s) (%s)" f (number_to_nat init) (list_to_list "Nat" number_to_nat xs))) in
  is (Term.to_string got) (number_to_nat output) msg

let test_foldr_add =
    let init = 5 in
    let xs = [2;3;4] in
    test_foldr_nat "add" init xs (List.fold_right (+) xs init) "foldr add 5 [2,3,4]"

let test_foldr_list f init xs output msg =
  let got = eval ~sym_def:sym_def (parse_term (sprintf "foldr Nat (List Nat) (%s) (%s) (%s)" f (list_to_list "Nat" number_to_nat init) (list_to_list "Nat" number_to_nat xs))) in
  is (Term.to_string got) (list_to_list "Nat" number_to_nat output) msg

let test_foldr_con =
  let init = [1] in
  let xs = [2;3;4] in
  test_foldr_list "con Nat" init xs (List.fold_right (fun x xs -> x :: xs) xs init) "foldr (con Nat) [1] [2,3,4]"*)

(*let test_foldl_flip xs msg =
  let got = eval ~debug:true ~sym_def:sym_def (parse_term (sprintf
    "foldl (List Nat) Nat (flip Nat (List Nat) (List Nat) (con Nat)) (nil Nat) (%s)"
    (list_to_natlist xs))) in
  is (Term.to_string got) (list_to_natlist (List.rev xs)) msg

let test_rev1 = test_foldl_flip [] "rev []";;*)
(*let test_rev2 = test_foldl_flip [0;1;1] "rev [0,1,1]";;
let test_rev3 = test_foldl_flip [4;2] "rev [4,2]";;

let test2 =
  print_string (Term.to_string (eval ~sym_def:sym_def (parse_term "foldl")))
*)

let test input output msg =
  let got = eval ~debug:true ~sym_def:sym_def (parse_term input) in
  is (Term.to_string got) output msg

(*let test_concat =
  let xs = [[1];[]] in
  test
    (sprintf
      "foldr (List Nat) (List Nat) (append Nat) (nil Nat) (%s)"
      (list_to_list "(List Nat)" list_to_natlist xs))
    (list_to_natlist (List.concat xs))
    "Why isn't this concat?"*)

let test_head =
  let xs = [] in
  test
    (sprintf
      "head Nat (%s)"
      (list_to_natlist xs))
    "undefined Nat"
    "Endless loop in head?"

(*let test_append =
  let xs = [1;2] in
  let ys = [3] in
  test
    (sprintf
      "append Nat (%s) (%s)"
      (list_to_natlist xs)
      (list_to_natlist ys))
    (list_to_natlist (xs @ ys))
    "append [1,2] [3]"*)


(*let test_enumFromTo =
  let n = 2 in
  let m = 6 in
  test
    (sprintf
      "foldNat (List Nat) (con Nat (%s)) (con Nat (%s) (nil Nat)) (sub (%s) (%s))"
      (number_to_nat n)
      (number_to_nat m)
      (number_to_nat m)
      (number_to_nat n))
    (list_to_natlist (List.range ~stop:`inclusive n m))
    "Is this really enumFromTo?"*)

(*let test_enumFromTo =
  let n = 1 in
  let m = 2 in
  test
    (sprintf
      "enumTo (foldl (Nat -> Nat) Nat (foldNat Nat) (add (%s)) (enumTo (%s)) (%s))"
      (number_to_nat m)
      (number_to_nat m)
      (number_to_nat n))
    (list_to_natlist (List.range ~stop:`inclusive n m))
    "Is this really enumFromTo?"*)

(*let test_enumFromTo =
  let n = 2 in
  let m = 6 in
  test
    (sprintf
      "con Nat (%s) (map Nat Nat succ (enumTo (sub (%s) (%s))))"
      (number_to_nat n)
      (number_to_nat m)
      (number_to_nat n))
    (list_to_natlist (List.range ~stop:`inclusive n m))
    "Is this really enumFromTo?"*)

(*let test_enumFromTo =
  let n = 1 in
  let m = 3 in
  test
    (sprintf
      "con Nat (%s) (map Nat Nat (add (%s)) (enumTo (sub (%s) (%s))))"
      (number_to_nat n)
      (number_to_nat n)
      (number_to_nat m)
      (number_to_nat n))
    (list_to_natlist (List.range ~stop:`inclusive n m))
    "Hand-written enumFromTo. Needs 5 components and has 9 leaves"*)




(*let test_enumFromTo =
  let n = 2 in
  let m = 6 in
  test
    (sprintf
      "map Nat Nat (sub (succ (%s))) (snd Nat (List Nat) (f_enumTo (pair_reverse_enum (%s))))"
      (number_to_nat m)
      (number_to_nat n))
    (list_to_natlist (List.range ~stop:`inclusive n m))
    "Is this really enumFromTo?"*)

(*let test_enumTo =
  let n = 3 in
  test
    (sprintf
      "rev Nat (snd Nat (List Nat) (pair_reverse_enum (%s)))"
      (number_to_nat n))
    (list_to_natlist (List.range ~stop:`inclusive 1 n))
    "why does enumTo not work?"*)

(*let test_enumFromTo =
  let n = 3 in
  test
    (sprintf
      "con Nat (foldNat Nat (mul (%s)) (%s) (mul (%s) (%s))) (nil Nat)"
      (number_to_nat n)
      (number_to_nat n)
      (number_to_nat n)
      (number_to_nat n))
    "no idea"
    "Debugging enumFromTo"*)

(*let test_enumTo = test
  (sprintf
    "rev Nat (snd Nat (List Nat) (foldNat (List Nat) (fanout (Pair Nat (List Nat)) Nat (List Nat) (uncurry Nat (List Nat) Nat (ignore Nat Nat (List Nat) succ)) (uncurry Nat (List Nat) Nat (con Nat))) (pair Nat (List Nat) (succ zero) (nil Nat)) (%s)))"
    (number_to_nat 2))
  (list_to_natlist [1;2])
  "enumTo"*)

(*let test_enumTo2 n xs = test
  (sprintf
    "pair Nat (List Nat) (succ (fst Nat (List Nat) (pair Nat (List Nat) (%s) (%s)))) (uncurry Nat (List Nat) (List Nat) (con Nat) (pair Nat (List Nat) (%s) (%s)))"
    (number_to_nat n)
    (list_to_natlist xs)
    (number_to_nat n)
    (list_to_natlist xs))
  (pair_to_pair "Nat" "List Nat" (number_to_nat (n+1), list_to_natlist (n::xs)))
  "(n, xs) -> (succ n, n :: xs)"*)

(*let test_enumTo2' = test_enumTo2 2 [1;0];;*)

(*let test_enumTo3 n = test
  (sprintf
    "foldNat (Pair Nat (List Nat)) f_enumTo (pair Nat (List Nat) (succ zero) (nil Nat)) (%s)"
    (number_to_nat n))
  (pair_to_pair "Nat" "List Nat" (number_to_nat (n+1), list_to_natlist (List.range ~stride:(-1) ~stop:`inclusive n 1)))
  "n -> (n+1, [n; n-1; n-2; ... ; 1])"

let test_enumTo3' = test_enumTo3 3;;*)

(*let test_add = test " { [Nat] : add $0 zero } (succ zero) " "succ zero" "1 + 0 with one lambda"
let test_sub = test " { [Nat] : sub $0 zero } (succ zero) " "succ zero" "1 - 0 with one lambda";;
let test_sub = test " { [Nat] [Nat] : sub $0 $1 } (zero) (succ zero) " "succ zero" "2 - 1 with lambda";;
let test_sub = test "sub (succ zero) zero" "succ zero" "1 - 0";;
let test_sub = test "sub (succ (succ zero)) (succ zero)" "succ zero" "2 - 1";;
let test_add = test (sprintf
      "add (%s) (%s)"
     (number_to_nat 2)
     (number_to_nat 1))
  (number_to_nat 3)
  "2 + 1";;*)

(*let test_fac = test
  (sprintf "prod (range (succ zero) (%s))" (number_to_nat 5))
  (number_to_nat 120)
  "factorial 5";;*)

(*let test_geq = test "natGeq zero (succ zero)" "false" "0 >= 1";;*)

(*let test_range = test "range zero (succ zero)" (list_to_natlist [0;1]) "[0..1]";;*)

(*let test_range =
  let got = eval ~debug:true ~sym_def:sym_def (parse_term (sprintf
    "range (%s) (%s)"
    (number_to_nat 0)
    (number_to_nat 1))) in
  is (Term.to_string got) (list_to_natlist [0;1]) "range 0 1"*)
