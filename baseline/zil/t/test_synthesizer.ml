open TestSimple;;
open Printf;;

open Zil.Lambda;;
open Zil.Parse;;
open Zil;;

plan 11;;
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

let const_sig = parse_type "@ @ #1 -> #0 -> #1";;
let const_def = parse_term "* * { [#1] [#0] : $1 }";;
let const_fun = name "const" (eval const_def);;
let () = Library.add_term "const" const_fun const_sig sym_lib;;


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
(* Test some of the library functions *)



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
  test_foldr_list "con Nat" init xs (List.fold_right (fun x xs -> x :: xs) xs init) "foldr (con Nat) [1] [2,3,4]"


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

(*(* TODO debugging *) let () = print_string "Printing free_lib...\n" in
   let () = print_free_lib free_lib in
   let () = print_string "________________\n" in
   let () = print_string "Printing sym_lib_uni...\n" in
   let () = print_sym_lib sym_lib_uni in
   let () = print_string "________________\n\n" in (* end *)*)

   let closed = (Synthesiser.enumerate queue sym_lib_uni free_lib nof_programs) in
   let satisfying = Synthesiser.filter_satisfying closed examples ~sym_def:(Library.get_lib_def sym_lib) in
   let () = print_string (sprintf "\n\n________________\n***Closed***\n%s" (String.concat "\n" (List.map Program.to_string closed))) in
   print_string (sprintf "\n\n_________________\n***Satisfying***\n%s" (String.concat "\n" (List.map Program.to_string satisfying)))


(*
(* easy test: try to generate map itself. Only three programs, because we cannot generate more from the components that we have *)
let () = print_string "\n\n\nGenerating map &1 &0 _1 _0\n\n"
let free_lib = Library.create ();;
let map_test = test_enumeration ~msg:"Try to generate map" list_map_sig free_lib 3;;
let () =  print_string (String.concat "\n" (List.map Program.to_string map_test));;
*)

(*
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

(*
(* try to generate const 1 *)
let () = print_string "\n\n\nGenerating const Nat $0 (succ zero) _0\n\n"
let free_lib = Library.create ();;
let example a input = ({
  term_info = (fun x ->
    match x with
    | 0 -> Some (parse_term input)
    | _ -> None);
  type_info = (fun x ->
    match x with
    | 0 -> Some (parse_type a)
    | _ -> None)
}, parse_term (number_to_nat 1))
let const_test =
  test_enumeration
    ~msg:"Generate const 1"
    (parse_type "@ #0 -> Nat")
    free_lib
    10
    ~examples:([example "Nat" (number_to_nat 6);
                example "List Nat" (list_to_list "Nat" number_to_nat []);
                example "List Nat" (list_to_list "Nat" number_to_nat [1])]);;
let () = print_string (String.concat "\n" (List.map Program.to_string const_test));;
*)

(*
(* try to generate map const 1 *)
let () = print_string "\n\n\nGenerating map &0 Nat (const 1) xs\n\n"
let free_lib = Library.create ();;
let example a input output = ({
  term_info = (fun x ->
    match x with
    | 0 -> Some (parse_term input)
    | _ -> None);
  type_info = (fun x ->
    match x with
    | 0 -> Some (parse_type a)
    | _ -> None)
}, parse_term output)
let map_const_test =
  test_enumeration
    ~msg:"Generate map const 1"
    (parse_type "@ List #0 -> List Nat")
    free_lib
    100
    ~examples:([example "Nat" (list_to_list "Nat" number_to_nat []) (list_to_list "Nat" number_to_nat []);
                example "List Nat" (list_to_list "(List Nat)" (list_to_list "Nat" number_to_nat) [ [3;2] ; [1] ; [1;1;1] ]) (list_to_list "Nat" number_to_nat [1;1;1]);
                example "Nat" (list_to_list "Nat" number_to_nat [1;2;3]) (list_to_list "Nat" number_to_nat [1;1;1])]);;
let () = print_string (String.concat "\n" (List.map Program.to_string map_const_test));;
*)

(*
(* try to generate length. 2000 closed programs are too few, 6000 takes too long *)
let () = print_string "\n\n\nGenerating length xs = Abs X. sum (map X Nat (const 1) xs)\n\n"
let free_lib = Library.create ();;
let example xs = ({
  term_info = (fun x ->
    match x with
    | 0 -> Some (parse_term (list_to_list "Nat" number_to_nat xs))
    | _ -> None);
  type_info = (fun x ->
    match x with
    | 0 -> Some (parse_type "Nat")
    | _ -> None)
}, parse_term (number_to_nat (List.length xs)));;
let length_test =
  test_enumeration
    ~msg:"Generate length"
    (parse_type "@ List #0 -> Nat")
    free_lib
    1000
    ~examples:(List.map example [[];[1];[1;2;3]]);;
let () = print_string (String.concat "\n" (List.map Program.to_string length_test));;
*)

(* Try to generate append *)
(* let () = print_string "\n\n\nGenerating append...\n\n"
let free_lib = Library.create ();;*)
let example (xs, ys) = ({
  term_info = (fun x ->
    match x with
    | 0 -> Some (parse_term (list_to_natlist xs))
    | 1 -> Some (parse_term (list_to_natlist ys))
    | _ -> None);
  type_info = (fun x ->
    match x with
    | 0 -> Some (parse_type "Nat")
    | _ -> None)
}, parse_term (list_to_natlist (List.append xs ys)));;
(*let append_test =
  test_enumeration
    ~msg:"Generate append"
    (parse_type "@ List #0 -> List #0 -> List #0")
    free_lib
    10
    ~examples:(List.map example
                 [([1;2;3],[]);
                  ([],[3;3;1]);
                  ([1],[2;3]);
                  ([1;2],[4;5])])
*)


(*
let () = print_string (sprintf "\n\n_____________\nJust testing evaluation. foldr Nat (List Nat) (con Nat) _0 _1 evaluates to %s\n" (Term.to_string (eval ~sym_def:sym_def ~free_def:(fst (example ([1],[2]))) (parse_term "foldr Nat (List Nat) (con Nat) _0 _1"))));;


let () = print_string (sprintf "Just testing evaluation. foldr Nat (List Nat) (con Nat) [1] [2] evaluates to %s\n\n" (Term.to_string (eval ~sym_def:sym_def (parse_term (sprintf "foldr Nat (List Nat) (%s) (%s)" (list_to_natlist [1]) (list_to_natlist [2]))))));;


let () = print_string
           (sprintf
             "map Nat Nat (const Nat Nat (succ zero)) [1,2,3] evaluates to %s\n"
             (Term.to_string
               (eval
                 ~sym_def:sym_def
                 (parse_term
                   (sprintf
                     "map Nat Nat (const Nat Nat (succ zero)) (%s)"
                     (list_to_natlist [1;2;3])))
             )));;

let () = print_string
           (sprintf
             "map Nat Nat (const Nat Nat (succ zero)) _0 evaluates to %s\n\n"
             (Term.to_string
               (eval
               ~sym_def:sym_def
               ~free_def:(fst (example ([1;2;3], [])))
               (parse_term "map Nat Nat (const Nat Nat (succ zero)) _0")
             )));;

let () = print_string
           (sprintf
             "add _0 _1 evaluates to %s\n"
             (Term.to_string
               (eval
               ~sym_def:sym_def
               ~free_def:(instantiate_free ([(number_to_nat 1); (number_to_nat 2)],[]))
               (parse_term "add _0 _1")
             )));;

let () = print_string
           (sprintf
             "add 1 2 evaluates to %s\n"
             (Term.to_string
               (eval
               ~sym_def:sym_def
               (parse_term
                 (sprintf "add (%s) (%s)"
                   (number_to_nat 1)
                   (number_to_nat 2)))
             )));;
*)
let const_one_sig = parse_type "Nat";;
let const_one_def = parse_term "succ zero";;
let const_one_fun = (eval ~sym_def:sym_def const_one_def);;
let () = Library.add_term "one" const_one_fun const_one_sig sym_lib;;
let () = print_string
           (sprintf
             "add 1 2 evaluates to %s\n"
             (Term.to_string
               (eval
               ~sym_def:sym_def
               ~hol_def:(instantiate_free ([(number_to_nat 1); (number_to_nat 2)],[]))
               (parse_term "add (succ zero) (succ (succ zero))")
            )));;

(*let () = print_string (Term.to_string const_one_def);;
let () = print_string "\n";;
let () = print_string (Term.to_string const_one_fun);;
let () = print_string "\n";;
let () = print_string (Term.to_string (eval (parse_term "succ zero")));;
let () = print_string "\n";;*)


(*
let () = print_string
           (sprintf
             "add ?0 ?1 evaluates to %s\n\n"
             (Term.to_string
               (eval
               ~sym_def:sym_def
               ~hol_def:(instantiate_free ([(number_to_nat 1); (number_to_nat 2)],[]))
               (parse_term "add ?0 ?1")
            )));;

  *)               
