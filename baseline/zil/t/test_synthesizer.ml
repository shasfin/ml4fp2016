open TestSimple;;
open Printf;;

open Zil.Lambda;;
open Zil.Parse;;
open Zil;;

plan 9;;
(******************************************************************************)
(* Define library *)

let sym_lib = Library.create ();;

(* We do not need to type the definitions of the library functions.
 * We can just put unit Term.t in it. They are used only for evaluation and evaluation does not use the annotations.
 * For evaluation we can do a map_label (fun _ -> unit), so it will typecheck *)

(* Types *)
(* Recursive lists *)
let list_sig = 1;;
let list_def = parse_type "@ #0 -> (#1 -> List #1 -> #0) -> #0";;
let () = Library.add_type "List" list_def list_sig sym_lib;;

(* Natural numbers *)
let nat_sig = 0;;
let nat_def = parse_type "@ #0 -> (Nat -> #0) -> #0";;
let () = Library.add_type "Nat" nat_def nat_sig sym_lib;;

(* Terms *)
(* list constructors *)
let list_nil_sig = parse_type "@ List #0";;
let list_nil_def = parse_term "* * { [#0] [#1 -> List #1 -> #0] : $1 }";;
let list_nil_fun = name "nil" (eval list_nil_def);;
let () = Library.add_term "nil" list_nil_fun list_nil_sig sym_lib;;

let list_con_sig = parse_type "@ #0 -> List #0 -> List #0";;
let list_con_def = parse_term "* { [#0] [List #0] : * { [#0] [#1 -> List #1 -> #0] : $0 $3 $2 } }";;
let list_con_fun = name "con" (eval list_con_def);;
let () = Library.add_term "con" list_con_fun list_con_sig sym_lib;;

(* nat constructors *)
let nat_zero_sig = parse_type "Nat";;
let nat_zero_def = parse_term "* { [#0] [Nat -> #0] : $1 }";;
let nat_zero_fun = name "zero" (eval nat_zero_def);;
let () = Library.add_term "zero" nat_zero_fun nat_zero_sig sym_lib;;

let nat_succ_sig = parse_type "Nat -> Nat";;
let nat_succ_def = parse_term "{ [Nat] : * { [#0] [Nat -> #0] : $0 $2 } }";;
let nat_succ_fun = name "succ" (eval nat_succ_def);;
let () = Library.add_term "succ" nat_succ_fun nat_succ_sig sym_lib;;

(* functions *)
let list_map_sig = parse_type "@ @ (#1 -> #0) -> List #1 -> List #0";;
let list_map_def = parse_term "* * { [#1 -> #0] [List #1] : $0 #0 (nil #0) { [#1] [List #1] : con #0 ($3 $1) (map #1 #0 $3 $0) } }";;
let list_map_fun = name "map" (eval list_map_def);;
let () = Library.add_term "map" list_map_fun list_map_sig sym_lib;;

let list_sum_sig = parse_type "List Nat -> Nat";;
let list_sum_def = parse_term "{ [List Nat] : $0 Nat zero { [Nat] [List Nat] : add $1 (sum $0) } }";;
let list_sum_fun = name "sum" (eval list_sum_def);;
let () = Library.add_term "sum" list_sum_fun list_sum_sig sym_lib;;

let list_foldr_sig = parse_type "@ @ (#1 -> #0 -> #0) -> #0 -> List #1 -> #0";;
let list_foldr_def = parse_term "* * { [#1 -> #0 -> #0] [#0] [List #1] : $0 #0 $1 { [#1] [List #1] : $4 $1 (foldr #1 #0 $4 $3 $0) } }";;
let list_foldr_fun = name "foldr" (eval list_foldr_def);;
let () = Library.add_term "foldr" list_foldr_fun list_foldr_sig sym_lib;;

let nat_add_sig = parse_type "Nat -> Nat -> Nat";;
let nat_add_def = parse_term "{ [Nat] [Nat] : $1 Nat $0 { [Nat] : succ (add $0 $1) } }";;
let nat_add_fun = name "add" (eval nat_add_def);;
let () = Library.add_term "add" nat_add_fun nat_add_sig sym_lib;;


(******************************************************************************)
(* Test some of the library functions *)
let sym_def = Library.get_lib_def sym_lib;;

(* syntax sugar for nats and lists of nats *)
let rec number_to_nat n = match n with
  | 0 -> "zero"
  | 1 -> "succ zero"
  | n -> sprintf "succ (%s)" (number_to_nat (n-1))
	
let rec list_to_list xs = match xs with
  | [] -> "nil Nat"
  | x::xs -> sprintf "con Nat (%s) (%s)" (number_to_nat x) (list_to_list xs)

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
  let got = eval ~sym_def:sym_def (parse_term (sprintf "sum (%s)" (list_to_list xs))) in
  is (Term.to_string got) (number_to_nat (List.fold_left (+) 0 xs)) msg
  
let test_sum1 = test_sum [] "sum []";;
let test_sum2 = test_sum [2] "sum [2]";;
let test_sum3 = test_sum [1;2;3] "sum [1;2;3]";;
let test_sum4 = test_sum [2;3;5;1] "sum [2;3;5;1]";;

(*
(******************************************************************************)
(* Prepare library for unification *)
let first_prog = Program.create ();;
let (sym_lib_uni, first_prog) = Synthesiser.prepare_lib sym_lib first_prog;;

(******************************************************************************)
(* Generate some simple programs (only type-based, without i/o *)

(* Print functions for debugging *)
let print_lib f g lib =
  Library.iter
    (fun i m a args -> print_string
      (sprintf "%s = %s : %s \n"
        (Term.to_string (f i))
        (Term.to_string m)
        (Type.to_string a)))
    (fun i a k -> print_string
      (sprintf "%s == %s :: %d \n"
        (Type.to_string (g i))
        (Type.to_string a)
        k))
    lib

let print_free_lib lib =
  print_lib
    (fun i -> Term.Free((), i))
    (fun i -> Type.Free i)
    lib

let print_sym_lib lib =
  print_lib
    (fun i -> Term.Sym((), i))
    (fun i -> Type.Sym(i, []))
    lib

let print_hol_lib lib =
  print_lib
    (fun i -> Term.Hol((), i))
    (fun i -> Type.Hol i)
    lib

(* general structure:
 * goal type
 * transform goal type and form free_lib (the signatures are the interesting part)
 * generate first program
 * enumerate programs *)
(* test_enumeration : ?msg:string -> Type.t -> (idx_free, unit) Library.t -> Program.t list *)
(* side effect: changes free_lib *)
let test_enumeration ?msg:(msg="Basic enumeration") goal_type free_lib ?examples:(examples=[]) nof_programs =
  let transform_type a =
    (* side effect: free_lib is built *)
    let rec deuniversalise a ity =
      (match a with
      | Type.All b ->
        let fresh_free = Type.Free ity in
        let () = Library.add_type ity fresh_free 0 free_lib in
        deuniversalise (Type.subst fresh_free 0 b) (ity+1)
      | _ -> a) in
    (* side effect: free_lib is built *)
    let rec dearrowise a ite =
      (match a with
      | Type.Arr (a, b) ->
        let fresh_free = Term.Free ((), ite) in
        let () = Library.add_term ite fresh_free a free_lib in
        dearrowise b (ite+1)
      | _ -> a) in

    dearrowise (deuniversalise goal_type 0) 0 in

  let prog = Program.reset first_prog (transform_type goal_type) in
  let queue = Queue.create () in
  let () = Queue.add prog queue in

(* TODO debugging *) let () = print_string "Printing free_lib...\n" in
   let () = print_free_lib free_lib in
   let () = print_string "________________\n" in
   let () = print_string "Printing sym_lib_uni...\n" in
   let () = print_sym_lib sym_lib_uni in
   let () = print_string "________________\n\n" in (* end *)

  Synthesiser.filter_satisfying (Synthesiser.enumerate queue sym_lib_uni free_lib nof_programs) examples ~sym_def:(Library.get_lib_def sym_lib)



(* easy test: try to generate map itself. Only three programs, because we cannot generate more from the components that we have *)
(*let () = print_string "\n\n\nGenerating map &1 &0 _1 _0\n\n"
let free_lib = Library.create ();;
let map_test = test_enumeration ~msg:"Try to generate map" list_map_sig free_lib 3;;
let () =  print_string (String.concat "\n" (List.map Program.to_string map_test));;*)

(* first test with I/O-examples. [zero] |-> [succ zero] *)
let () = print_string "\n\n\nGenerating map Nat Nat succ _0...\n\n"
let free_lib = Library.create ();;
let input = {
  term_info = (fun x ->
    match x with
    | 0 -> Some (parse_term "con Nat zero (nil Nat)")
    | n -> None);
  type_info = (fun _ -> None)
};;
let output = parse_term "con Nat (succ zero) (nil Nat)";;
let map_test_2 =
  test_enumeration
    ~msg:"Try to generate map Nat Nat succ _0"
    (parse_type "List Nat -> List Nat")
    free_lib
    4
    ~examples:[(input,output)];;
let () = print_string (String.concat "\n" (List.map Program.to_string map_test_2));;


*)