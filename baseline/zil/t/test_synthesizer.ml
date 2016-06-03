open TestSimple;;
open Printf;;
open Core.Std;;

open Zil.Lambda;;
open Zil.Parse;;
open Zil;;


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
(* Prepare library for unification *)
let first_prog = Program.create ();;
let (sym_lib_uni, first_prog) = Synthesiser.prepare_lib sym_lib first_prog;;

(******************************************************************************)
(* Generate some simple programs *)


(* general structure:
 * goal type
 * transform goal type and form free_lib (the signatures are the interesting part)
 * generate first program
 * enumerate programs *)

(* test_enumeration : ?msg:string -> Type.t -> (idx_free, unit) Library.t -> Program.t list *)
(* side effect: changes free_lib *)
(* examples is a list of (input,output) pair, where input is a (mm,aa) pair
 * it has hence the type ((string list * string list) * string) list *)
let test_enumeration ?msg:(msg="Basic enumeration") goal_type free_lib ?examples:(examples=[]) nof_programs =
  (* TODO debugging *) let () = printf "\n\n\n%s...\n" msg in (* end *)
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
  let queue = Heap.create ~min_size:100 ~cmp:Program.compare () in
  let () = Heap.add queue prog in

(*(* TODO debugging *) let () = print_string "Printing free_lib...\n" in
   let () = print_free_lib free_lib in
   let () = print_string "\n________________\n" in
   let () = print_string "Printing sym_lib_uni...\n" in
   let () = print_sym_lib sym_lib_uni in
   let () = print_string "\n________________\n\n" in (* end *)*)

   let examples =
     List.map
       ~f:(fun (input, output) -> (instantiate_free input, parse_term output))
       examples in
   let satisfying = Synthesiser.enumerate_satisfying queue ~sym_lib:sym_lib_uni ~free_lib:free_lib ~examples:examples nof_programs in
   (*let closed = (Synthesiser.enumerate queue sym_lib_uni free_lib nof_programs) in
   let satisfying = Synthesiser.filter_satisfying closed examples ~sym_def:(Library.get_lib_def sym_lib) in
   let () = print_string (sprintf "\n***Closed***\n________________\n%s\n" (String.concat ~sep:"\n" (List.map ~f:Program.to_string closed))) in*)
   printf "\n***Satisfying***\n________________\n%s\n" (String.concat ~sep:"\n" (List.map ~f:Program.to_string satisfying))



(*(* easy test: try to generate map itself. Only three programs, because we cannot generate more from the components that we have *)
let free_lib = Library.create ();;
let map_test =
  test_enumeration
    ~msg:"Generating map itself only based on type information"
    (parse_type "@ @ (#1 -> #0) -> List #1 -> List #0")
    free_lib
    11;;*)


(*(* first test with I/O-examples. [zero] |-> [succ zero] *)
let free_lib = Library.create ();;
let map_test_2 =
  let example (input, output) =
    (([list_to_natlist input], []), list_to_natlist output) in
  test_enumeration
    ~msg:"Try to generate map Nat Nat succ _0"
    (parse_type "List Nat -> List Nat")
    free_lib
    1
    ~examples:(List.map ~f:example
               [([],[]);
                ([1;2;3],[2;3;4]);
                ([4;2;6],[5;3;7])]);;*)

(*(* try to generate const 1 *)
let free_lib = Library.create ();;
let const_test =
  let example (a, input) = (([input], [a]), number_to_nat 1) in
  test_enumeration
    ~msg:"Generate const 1"
    (parse_type "@ #0 -> Nat")
    free_lib
    10
    ~examples:(List.map ~f:example
               [("Nat", (number_to_nat 6));
                ("List Nat", (list_to_list "Nat" number_to_nat []));
                ("List Nat", (list_to_list "Nat" number_to_nat [1]))]);;*)

(*(* try to generate map const 1 *)
let free_lib = Library.create ();;
let map_const_test =
  let example (a, input, output) = (([input],[a]),output) in
  test_enumeration
    ~msg:"Generate map &0 Nat (const 1) xs"
    (parse_type "@ List #0 -> List Nat")
    free_lib
    1
    ~examples:(List.map ~f:example 
               [("Nat", (list_to_list "Nat" number_to_nat []), (list_to_list "Nat" number_to_nat []));
                ("List Nat", (list_to_list "(List Nat)" (list_to_list "Nat" number_to_nat) [ [3;2] ; [1] ; [1;1;1] ]), (list_to_list "Nat" number_to_nat [1;1;1]));
                ("Nat", (list_to_list "Nat" number_to_nat [1;2;3]), (list_to_list "Nat" number_to_nat [1;1;1]))]);;*)

(*(* try to generate length. 2000 closed programs are too few, 6000 takes too long *)
let free_lib = Library.create ();;
let length_test =
  let example (a, input, output) = (([input],[a]), number_to_nat output) in
  test_enumeration
    ~msg:"Generate length"
    (parse_type "@ List #0 -> Nat")
    free_lib
    1
    ~examples:(List.map ~f:example
               [("Nat", list_to_natlist [], List.length []);
                ("Nat", list_to_natlist [1], List.length [1]);
                ("Nat", list_to_natlist [1;2;3], List.length [1;2;3])]);;*)


(*(* Try to generate append *)
let free_lib = Library.create ();;
let append_test =
    let example (xs, ys) = (([list_to_natlist xs; list_to_natlist ys],["Nat"]), list_to_natlist (List.append xs ys)) in
  test_enumeration
    ~msg:"Generate append"
    (parse_type "@ List #0 -> List #0 -> List #0")
    free_lib
    1
    ~examples:(List.map ~f:example
                 [([1;2;3],[]);
                  ([],[3;3;1]);
                  ([1],[2;3]);
                  ([1;2],[4;5])]);;*)

(*(* Try to generate reverse *)
let free_lib = Library.create ();;
let reverse_test =
  let example xs = (([list_to_natlist xs],["Nat"]), list_to_natlist (List.rev xs)) in
  test_enumeration
    ~msg:"Generate reverse"
    (parse_type "@ List #0 -> List #0")
    free_lib
    1 (* result generated after 1000 closed programs with nil, con, zero, succ, map, foldr, foldl, flip, add, sum in the library *)
    ~examples:(List.map ~f:example
               [[1;2;3];
                [2;5;1];
                [1;1];
                [5];
                [3;1]]);;*)

(* Try to generate factorial *)
let free_lib = Library.create ();;
let factorial_test =
    let example x = (([number_to_nat x],[]), number_to_nat (List.fold_right ~f:(fun x acc -> x*acc) ~init:1 (List.range ~stop:`inclusive 1 x))) in
  test_enumeration
    ~msg:"Generate factorial"
    (parse_type "Nat -> Nat")
    free_lib
    1 
    ~examples:(List.map ~f:example
               [1;
                2;
                3]);;

(*(* Try to generate enumFromTo *)
let free_lib = Library.create ();;
let reverse_test =
    let example (x,y) = (([number_to_nat x; number_to_nat y],[]), list_to_natlist (List.range ~stop:`inclusive x y)) in
  test_enumeration
    ~msg:"Generate enumFromTo"
    (parse_type "Nat -> Nat -> List Nat")
    free_lib
    1 (* result generated after 1000 closed programs with nil, con, zero, succ, map, foldr, foldl, flip, add, sum in the library *)
    ~examples:(List.map ~f:example
               [(1,3);
                (0,4);
                (4,5);
                (2,4)]);;*)

