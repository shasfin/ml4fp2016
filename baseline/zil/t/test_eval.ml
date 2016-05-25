open Printf;;
open Zil.Lambda;;
open Zil.Parse;;
open Zil;;


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
  | x::xs -> sprintf "con %s (%s) (%s)" a (f x) (list_to_list a f xs)

(* Convert [1;2;3] to a list of nat *)
let list_to_natlist = list_to_list "Nat" number_to_nat


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

(*let test_eval = eval ~debug:true ~sym_def:sym_def (parse_term (sprintf "foldl Nat Nat add zero %s" (list_to_natlist [1;2;3])));;*)

(*let test_eval = eval ~debug:true ~sym_def:sym_def (parse_term (sprintf "foldr Nat Nat add zero %s" (list_to_natlist [1;2;3])));;*)

(*let test_eval = eval ~debug:true ~sym_def:sym_def (parse_term (sprintf
      "foldl (List Nat) Nat (flip Nat (List Nat) (List Nat) (con Nat)) (nil Nat) (%s)"
      (list_to_natlist [1;2;3])));;*)

(*let test_eval = eval ~debug:true ~sym_def:sym_def (parse_term (sprintf
      "foldl Nat Nat (flip Nat Nat Nat add) zero (%s)"
      (list_to_natlist [1;2;3])));;*)

let test_eval = eval ~debug:true ~sym_def:sym_def (parse_term (sprintf
      "foldr Nat Nat (flip Nat Nat Nat add) zero (%s)"
      (list_to_natlist [1;2;3])));;

(*let test_eval = eval ~debug:true ~sym_def:sym_def (parse_term (sprintf
      "foldr Nat (List Nat) (con Nat) (nil Nat) (%s)"
      (list_to_natlist [1;2;3])));;*)

(*let test_flip = eval ~debug:true ~sym_def:sym_def (parse_term
      "flip Nat (List Nat) (List Nat) (con Nat) (nil Nat) zero");;*)

(*let test_flip = eval ~debug:true ~sym_def:sym_def (parse_term
      "flip Nat Nat Nat add zero zero");;*)

(*let test_typechecking =
  let annotated = well ~sym_sig:sym_sig (parse_term (sprintf
      "foldl (List Nat) Nat (flip Nat (List Nat) (List Nat) (con Nat)) (nil Nat) (%s)"
      (list_to_natlist [1;2;3]))) in
  let a = Term.extract_label annotated in
  (match a with
  | Some a -> print_string (Type.to_string a)
  | None -> print_string "Something went wrong")*)
