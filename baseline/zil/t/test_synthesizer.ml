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
(* Prepare library for unification *)
let first_prog = Program.create ();;
let (sym_lib_uni, first_prog) = Synthesiser.prepare_lib sym_lib first_prog;;

(******************************************************************************)
(* Transform goal type - changes free_lib *)
 let transform_type free_lib a =
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

    dearrowise (deuniversalise a 0) 0


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
(* components is the list of components used for synthesis. For evaluation the whole library.tm is used *)
let test_enumeration ?msg:(msg="Basic enumeration") goal_type free_lib ?examples:(examples=[]) ?components:(components=[]) nof_programs =

  let sym_lib_comp = (match components with
    | [] -> sym_lib_uni
    | _ -> (let sym_lib_comp = Library.create () in
            let () = Library.iter_types
              (fun i a k -> Library.add_type i a k sym_lib_comp)
              sym_lib_uni in
            let () = List.iter
              ~f:(fun i -> let (m, a, args) = Library.lookup_term sym_lib_uni i in
                        Library.add_term i m a ~typ_args:args sym_lib_comp)
              components in
            sym_lib_comp)) in

  (* TODO debugging *) let () = printf "\n\n\n%s...\n" msg in (* end *)

  let prog = Program.reset first_prog (transform_type free_lib goal_type) in
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
       ~f:(fun (input, output) -> (instantiate_free input, eval ~sym_def:sym_def (parse_term output)))
       examples in
   let satisfying = Synthesiser.enumerate_satisfying queue ~sym_lib:sym_lib_comp ~free_lib:free_lib ~sym_def:sym_def ~examples:examples nof_programs in
   (*let closed = (Synthesiser.enumerate queue sym_lib_uni free_lib nof_programs) in
   let satisfying = Synthesiser.filter_satisfying closed examples ~sym_def:(Library.get_lib_def sym_lib) in
   let () = print_string (sprintf "\n***Closed***\n________________\n%s\n" (String.concat ~sep:"\n" (List.map ~f:Program.to_string closed))) in*)
   printf "\n***Satisfying***\n________________\n%s\n" (String.concat ~sep:"\n" (List.map ~f:Program.to_string satisfying))



let test_hypothesis1 ?msg:(msg="First order enumeration") goal_type (holes, template) ?examples:(examples=[]) ?components:(components=[]) nof_programs =
  let free_lib = Library.create () in

  let sym_lib_comp = (match components with
    | [] -> sym_lib_uni
    | _ -> (let sym_lib_comp = Library.create () in
            let () = Library.iter_types
              (fun i a k -> Library.add_type i a k sym_lib_comp)
              sym_lib_uni in
            let () = List.iter
              ~f:(fun i -> let (m, a, args) = Library.lookup_term sym_lib_uni i in
                        Library.add_term i m a ~typ_args:args sym_lib_comp)
              components in
            sym_lib_comp)) in

  (* TODO debugging *) let () = printf "\n\n\n%s...\n" msg in (* end *)


  let prog = Program.reset first_prog (transform_type free_lib goal_type) in
  let (prog, mm) = List.fold_left
    ~f:(fun (prog, acc) a ->
      let (mi, prog) = Program.get_fresh_term_hol (parse_type a) prog in
      (prog, mi::acc))
    ~init:(prog,[])
    holes in
  let m = parse_term (template) in (* XXX this is a hack. It assumes that fresh holes are ?1, ?2, ?3 and so on *)
  let get_idx = function
    | Term.Hol (_, i) -> i
    | _ -> invalid_arg "This should be a hole" in
  let hol_fun = List.map
    ~f:(fun m -> (get_idx m, Term.extract_label m))
    mm in
  let hol_sig = {
    type_info = (fun x -> None);
    term_info = (fun x -> List.Assoc.find hol_fun x);
  } in
  let m = well ~hol_sig:hol_sig ~sym_sig:(Library.get_lib_sig sym_lib) m in
  let m = Term.map_label
    (fun x -> (match x with
      | Some x -> x
      | None -> invalid_arg "Problem typechecking a pattern"))
    m in
  let prog = Program.expand_current_hol m prog in

  let queue = Heap.create ~min_size:100 ~cmp:Program.compare () in
  let () = Heap.add queue prog in

  let examples =
    List.map
      ~f:(fun (input, output) -> (instantiate_free input, eval ~sym_def:sym_def (parse_term output)))
      examples in
  let satisfying = Synthesiser.enumerate_satisfying queue ~sym_lib:sym_lib_comp ~free_lib:free_lib ~sym_def:sym_def ~examples:examples nof_programs in
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
    1
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

(*(* try to generate length *)
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
                 [([1],[2;3]);
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
                [2;5;1]]);;*)

(*(* Try to generate factorial *)
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
                3]);;*)

(*(* Try to generate replicate *)
let free_lib = Library.create ();;
let replicate_test =
  let example (x, n) = 
    let rec replicate n = match n with
      | 0 -> []
      | n -> x::(replicate (n-1)) in
      
      (([number_to_nat x; number_to_nat n],["Nat"]), list_to_natlist (replicate n)) in
  test_enumeration
    ~msg:"Generate replicate"
    (parse_type "@ #0 -> Nat -> List #0")
    free_lib
    1 
    ~examples:(List.map ~f:example
               [(1,0);
                (0,2);
                (3,1)]);;*)

(*(* Try to generate enumFromTo *)
let free_lib = Library.create ();;
let enumFromTo_test =
    let example (x,y) = (([number_to_nat x; number_to_nat y],[]), list_to_natlist (List.range ~stop:`inclusive x y)) in
  test_enumeration
    ~msg:"Generate enumFromTo"
    (parse_type "Nat -> Nat -> List Nat")
    free_lib
    1 
    ~examples:(List.map ~f:example
               [(2,3);
                (1,3)]);;*)

(*(* Try to generate enumFromTo *)
let enumFromTo_test =
    let example (x,y) = (([number_to_nat x; number_to_nat y],[]), list_to_natlist (List.range ~stop:`inclusive x y)) in
  test_hypothesis1
    ~msg:"Generate enumFromTo"
    (parse_type "Nat -> Nat -> List Nat")
    (["Nat";"List Nat"], "map Nat Nat (add ?1) ?2")
    1
    ~components:["const";
                 "flip";
                 "curry";
                 "uncurry";
                 "fanout";
                 "ignore";
                 "zero";
                 "succ";
                 "true";
                 "false";
                 "pair";
                 "fst";
                 "snd";
                 "foldr";
                 "foldl";
                 "foldNat";
                 "sub";
                 "length";
                 "replicate";
                 "append";
                 "rev";
                 "concat";
                 "enumTo"]

    ~examples:(List.map ~f:example
               [(2,3);
                (1,3)]);;*)


(*(* Try to generate enumFromTo *)
let free_lib = Library.create ();;
let enumFromTo_test =
  let example (x,y) = (([number_to_nat x; number_to_nat y],[]), list_to_natlist (List.range ~stop:`inclusive x y)) in
  let goal_type = parse_type "Nat -> Nat -> List Nat" in
  let prog = Program.reset first_prog (transform_type free_lib goal_type) in
  let (m1, prog) = Program.get_fresh_term_hol (parse_type "Nat") prog in
  let (m2, prog) = Program.get_fresh_term_hol (parse_type "List Nat") prog in
  let m = parse_term (sprintf "con Nat (%s) (%s)" (Term.to_string m1) (Term.to_string m2)) in
  let h1 = (match m1 with Term.Hol (_, i) -> i | _ -> 0) in
  let h2 = (match m2 with Term.Hol (_, i) -> i | _ -> 0) in
  let hol_sig_terms = (fun x ->
    (if x = h1
    then Some (Term.extract_label m1)
    else if x = h2
    then Some (Term.extract_label m2)
    else None)) in
  let hol_sig = {
    type_info = (fun x -> None);
    term_info = hol_sig_terms;
  } in
  let m = well ~hol_sig:hol_sig ~sym_sig:(Library.get_lib_sig sym_lib) m in
  let m = Term.map_label
    (fun x -> (match x with
      | Some x -> x
      | None -> invalid_arg "Problem typechecking a pattern"))
    m in
  let prog = Program.expand_current_hol m prog in

(*free_lib prog  ?examples:(examples=[]) ?components:(components=[]) nof_programs *)

  test_hypothesis1
    ~msg:"Generate enumFromTo"
    free_lib
    prog
    1
    ~components:["const";
                 "flip";
                 "curry";
                 "uncurry";
                 "fanout";
                 "ignore";
                 "zero";
                 "succ";
                 "true";
                 "false";
                 "pair";
                 "fst";
                 "snd";
                 "map";
                 "foldr";
                 "foldl";
                 "foldNat";
                 "sub";
                 "add";
                 "length";
                 "replicate";
                 "append";
                 "rev";
                 "concat";
                 "enumTo"]

    ~examples:(List.map ~f:example
               [(2,3);
                (1,3)]);;*)

(*(* Try to generate enumFromTo *)
let free_lib = Library.create ();;
let enumFromTo_test =
  let example (x,y) = (([number_to_nat x; number_to_nat y],[]), list_to_natlist (List.range ~stop:`inclusive x y)) in
  let goal_type = parse_type "Nat -> Nat -> List Nat" in
  let prog = Program.reset first_prog (transform_type free_lib goal_type) in
  let (m1, prog) = Program.get_fresh_term_hol (parse_type "List Nat -> List Nat") prog in
  let (m2, prog) = Program.get_fresh_term_hol (parse_type "Nat") prog in
  let (m3, prog) = Program.get_fresh_term_hol (parse_type "List Nat") prog in
  let m = parse_term (sprintf "(%s) (map Nat Nat (add (%s)) (%s))" (Term.to_string m1) (Term.to_string m2) (Term.to_string m3)) in
  let get_idx = function
    | Term.Hol (_, i) -> i
    | _ -> 0 in
  let h1 = get_idx m1 in
  let h2 = get_idx m2 in
  let h3 = get_idx m3 in 
  let hol_sig_terms = (fun x ->
    (if x = h1
    then Some (Term.extract_label m1)
    else if x = h2
    then Some (Term.extract_label m2)
    else if x = h3
    then Some (Term.extract_label m3)
    else None)) in
  let hol_sig = {
    type_info = (fun x -> None);
    term_info = hol_sig_terms;
  } in
  let m = well ~hol_sig:hol_sig ~sym_sig:(Library.get_lib_sig sym_lib) m in
  let m = Term.map_label
    (fun x -> (match x with
      | Some x -> x
      | None -> invalid_arg "Problem typechecking a pattern"))
    m in
  let prog = Program.expand_current_hol m prog in

(*free_lib prog  ?examples:(examples=[]) ?components:(components=[]) nof_programs *)

  test_hypothesis1
    ~msg:"Generate enumFromTo"
    free_lib
    prog
    1
    ~components:["const";
                 "nil";
                 "con";
                 "zero";
                 "succ";
                 "true";
                 "false";
                 "pair";
                 "fst";
                 "snd";
                 "sub";
                 "add";
                 "length";
                 "replicate";
                 "append";
                 "rev";
                 "concat";
                 "enumTo"]

    ~examples:(List.map ~f:example
               [(2,3);
                (1,3)]);;*)

(*(* Try to generate enumFromTo *)
let free_lib = Library.create ();;
let enumFromTo_test =
  let example (x,y) = (([number_to_nat x; number_to_nat y],[]), list_to_natlist (List.range ~stop:`inclusive x y)) in
  let goal_type = parse_type "Nat -> Nat -> List Nat" in
  let prog = Program.reset first_prog (transform_type free_lib goal_type) in
  let (m1, prog) = Program.get_fresh_term_hol (parse_type "Nat") prog in
  let (m2, prog) = Program.get_fresh_term_hol (parse_type "List Nat -> List Nat") prog in
  let (m3, prog) = Program.get_fresh_term_hol (parse_type "Nat") prog in
  let m = parse_term (sprintf "con Nat (%s) ((%s) (enumTo (%s)))" (Term.to_string m1) (Term.to_string m2) (Term.to_string m3)) in
  let get_idx = function
    | Term.Hol (_, i) -> i
    | _ -> 0 in
  let h1 = get_idx m1 in
  let h2 = get_idx m2 in
  let h3 = get_idx m3 in 
  let hol_sig_terms = (fun x ->
    (if x = h1
    then Some (Term.extract_label m1)
    else if x = h2
    then Some (Term.extract_label m2)
    else if x = h3
    then Some (Term.extract_label m3)
    else None)) in
  let hol_sig = {
    type_info = (fun x -> None);
    term_info = hol_sig_terms;
  } in
  let m = well ~hol_sig:hol_sig ~sym_sig:(Library.get_lib_sig sym_lib) m in
  let m = Term.map_label
    (fun x -> (match x with
      | Some x -> x
      | None -> invalid_arg "Problem typechecking a pattern"))
    m in
  let prog = Program.expand_current_hol m prog in

(*free_lib prog  ?examples:(examples=[]) ?components:(components=[]) nof_programs *)

  test_hypothesis1
    ~msg:"Generate enumFromTo"
    free_lib
    prog
    1
    ~components:["const";
                 "zero";
                 "succ";
                 "true";
                 "false";
                 "pair";
                 "fst";
                 "snd";
                 "map";
                 "foldr";
                 "foldl";
                 "sub";
                 "add";
                 "length";
                 "replicate";
                 "append";
                 "rev";
                 "concat"]

    ~examples:(List.map ~f:example
               [(2,3);
                (1,3)]);;*)




(*(* Try to generate enumTo *)
let free_lib = Library.create ();;
let enumTo_test =
    let example x = (([number_to_nat x],[]), list_to_natlist (List.range ~stop:`inclusive 1 x)) in
  test_enumeration
    ~msg:"Generate enumTo"
    (parse_type "Nat -> List Nat")
    free_lib
    1 
    ~examples:(List.map ~f:example
               [2;
                3]);;*)

(*(* Try to generate enumTo step by step *)
let free_lib = Library.create ();;
let enumTo1_test =
    let example x = (([number_to_nat x],[]), pair_to_pair "Nat" "List Nat" (number_to_nat x, list_to_natlist (List.range ~stop:`inclusive 1 x))) in
  test_enumeration
    ~msg:"Generate enumTo1"
    (parse_type "Nat -> List Nat")
    free_lib
    1 
    ~examples:(List.map ~f:example
               [2;
                3]);;*)

(*(* Try to generate enumTo step by step -- the function for foldNat -- successful *)
let free_lib = Library.create ();;
let enumTo2_test =
    let example (x, xs) = (([pair_to_pair "Nat" "List Nat" ((number_to_nat x), (list_to_natlist xs))],[]), pair_to_pair "Nat" "List Nat" (number_to_nat (x+1), list_to_natlist (x::xs))) in
  test_enumeration
    ~msg:"Generate enumTo2 - fanout (uncurry (ignore succ)) (uncurry con)"
    (parse_type "Pair Nat (List Nat) -> Pair Nat (List Nat)")
    free_lib
    1 
    ~examples:(List.map ~f:example
               [(2,[1;0]);
                (3,[1;2])]);;*)

(*(* Try to generate enumTo step by step -- foldNat f_enumTo (succ zero, nil) n *)
let free_lib = Library.create ();;
let enumTo3_test =
    let example x = (([number_to_nat x],[]), pair_to_pair "Nat" "List Nat" (number_to_nat (x+1), list_to_natlist (List.range ~stride:(-1) ~stop:`inclusive x 1))) in
  test_enumeration
    ~msg:"Generate enumTo3"
    (parse_type "Nat -> Pair Nat (List Nat)")
    free_lib
    1 
    ~examples:(List.map ~f:example
               [2;
                3]);;*)

(*(* Try to generate enumTo step by step -- snd (foldNat f_enumTo (succ zero, nil) n)  -- takes more than 10 times more than enumTo3 *)
let free_lib = Library.create ();;
let enumTo4_test =
    let example x = (([number_to_nat x],[]), list_to_natlist (List.range ~stride:(-1) ~stop:`inclusive x 1)) in
  test_enumeration
    ~msg:"Generate enumTo4"
    (parse_type "Nat -> List Nat")
    free_lib
    1 
    ~examples:(List.map ~f:example
               [2;
                3]);;*)

(*(* Try to generate concat *)
let free_lib = Library.create ();;
let concat_test =
    let example xs = (([list_to_list "(List Nat)" list_to_natlist xs],["Nat"]), list_to_natlist (List.concat xs)) in
  test_enumeration
    ~msg:"Generate concat"
    (parse_type "@ List (List #0) -> List #0")
    free_lib
    1 
    ~examples:(List.map ~f:example 
               [[[1];[]];
                [[1;2];[3]]]);;*)

(*(* Try to generate stutter *)
let free_lib = Library.create ();;
let stutter_test =
    let rec stutter xs = (match xs with
      | [] -> []
      | x::xs -> x::x::(stutter xs)) in
    let example xs = (([list_to_natlist xs],["Nat"]), list_to_natlist (stutter xs)) in
  test_enumeration
    ~msg:"Generate stutter"
    (parse_type "@ List #0 -> List #0")
    free_lib
    1
    ~components:["const";
                 "nil";
                 "con";
                 "zero";
                 "succ";
                 "true";
                 "false";
                 "pair";
                 "fst";
                 "snd";
                 "sub";
                 "add";
                 "length";
                 "replicate";
                 "append";
                 "rev";
                 "concat";
                 "enumTo"]
    ~examples:(List.map ~f:example 
               [[1];
                [1;2;3]]);;*)

(*(* Try to generate stutter *)
let stutter_test =
    let rec stutter xs = (match xs with
      | [] -> []
      | x::xs -> x::x::(stutter xs)) in
    let example xs = (([list_to_natlist xs],["Nat"]), list_to_natlist (stutter xs)) in
  test_hypothesis1
    ~msg:"Generate stutter"
    (parse_type "@ List #0 -> List #0")
    (["List (List &0) -> List &0"; "&0 -> List &0"; "List &0"],"?1 (map &0 (List &0) ?2 ?3)")
    1
    ~components:["const";
                 "nil";
                 "con";
                 "zero";
                 "succ";
                 "true";
                 "false";
                 "pair";
                 "fst";
                 "snd";
                 "sub";
                 "add";
                 "length";
                 "replicate";
                 "append";
                 "rev";
                 "concat";
                 "enumTo"]
    ~examples:(List.map ~f:example 
               [[1];
                [1;2;3]]);;*)

(* Try to generate stutter *)
let stutter_test =
    let (a, first_prog) = Program.get_fresh_type_hol first_prog in
    let (b, first_prog) = Program.get_fresh_type_hol first_prog in
    let rec stutter xs = (match xs with
      | [] -> []
      | x::xs -> x::x::(stutter xs)) in
    let example xs = (([list_to_natlist xs],["Nat"]), list_to_natlist (stutter xs)) in
  test_hypothesis1
    ~msg:"Generate stutter"
    (parse_type "@ List #0 -> List #0")
    ([sprintf "List %s -> List &0" (Type.to_string b);
      sprintf "%s -> %s" (Type.to_string a) (Type.to_string b);
      sprintf "List %s" (Type.to_string a)],
     sprintf "?1 (map %s %s ?2 ?3)" (Type.to_string a) (Type.to_string b))
    1
    ~components:["const";
                 "nil";
                 "con";
                 "zero";
                 "succ";
                 "true";
                 "false";
                 "pair";
                 "fst";
                 "snd";
                 "sub";
                 "add";
                 "length";
                 "replicate";
                 "append";
                 "rev";
                 "concat";
                 "enumTo"]
    ~examples:(List.map ~f:example 
               [[1];
                [1;2;3]]);;


(*(* Try to generate stutter *)
let stutter_test =
    let rec stutter xs = (match xs with
      | [] -> []
      | x::xs -> x::x::(stutter xs)) in
    let example xs = (([list_to_natlist xs],["Nat"]), list_to_natlist (stutter xs)) in
  test_hypothesis1
    ~msg:"Generate stutter"
    (parse_type "@ List #0 -> List #0")
    (["List (List &0)"],"concat &0 ?1")
    1
    ~components:["const";
                 "flip";
                 "curry";
                 "uncurry";
                 "fanout";
                 "ignore";
                 "zero";
                 "succ";
                 "true";
                 "false";
                 "pair";
                 "fst";
                 "snd";
                 "map";
                 "foldr";
                 "foldl";
                 "foldNat";
                 "sub";
                 "length";
                 "replicate";
                 "append";
                 "rev";
                 "enumTo"]
    ~examples:(List.map ~f:example 
               [[1];
                [1;2;3]]);;*)



(*(* Try to generate sum *)
let free_lib = Library.create ();;
let sum_test =
  let sum xs = List.fold_right ~f:(+) ~init:0 xs in
  let example xs = (([list_to_natlist xs],[]), number_to_nat (sum xs)) in
  test_enumeration
    ~msg:"Generate sum"
    (parse_type "List Nat -> Nat")
    free_lib
    1
    ~components:["nil";
                 "con";
                 "zero";
                 "succ";
                 "true";
                 "false";
                 "pair";
                 "fst";
                 "snd";
                 "map";
                 "foldr";
                 "foldl";
                 "range";
                 "foldNat";
                 "add";
                 "replicate";
                 "concat"]
    ~examples:(List.map ~f:example
               [[1;2;3];
                [2;2]]);;*)

(*(* Try to generate sum *)
let free_lib = Library.create ();;
let sum_test =
  let sum xs = List.fold_right ~f:(+) ~init:0 xs in
  let example xs = (([list_to_natlist xs],[]), number_to_nat (sum xs)) in
  test_enumeration
    ~msg:"Generate sum"
    (parse_type "List Nat -> Nat")
    free_lib
    1
    ~components:["const";
                 "flip";
                 "curry";
                 "uncurry";
                 "fanout";
                 "ignore";
                 "nil";
                 "con";
                 "zero";
                 "succ";
                 "true";
                 "false";
                 "pair";
                 "fst";
                 "snd";
                 "map";
                 "foldr";
                 "foldl";
                 "range";
                 "foldNat";
                 "sub";
                 "add";
                 "length";
                 "replicate";
                 "append";
                 "rev";
                 "concat";
                 "enumTo"]
    ~examples:(List.map ~f:example
               [[1;2;3];
                [3;2]]);;*)

(*(* Try to generate multfirst *)
let free_lib = Library.create ();;
let multfirst_test =
    let example xs = (([list_to_natlist xs],["Nat"]), list_to_natlist (List.map ~f:(fun _ -> List.hd_exn xs) xs)) in
  test_enumeration
    ~msg:"Generate multfirst"
    (parse_type "@ List #0 -> List #0")
    free_lib
    1
    ~components:["const";
                 "flip";
                 "curry";
                 "uncurry";
                 "fanout";
                 "ignore";
                 "nil";
                 "con";
                 "zero";
                 "succ";
                 "true";
                 "false";
                 "pair";
                 "fst";
                 "snd";
                 "map";
                 "foldr";
                 "foldl";
                 "range";
                 "sum";
                 "prod";
                 "foldNat";
                 "natEq";
                 "natGeq";
                 "sub";
                 "add";
                 "mul";
                 "length";
                 "replicate";
                 "append";
                 "rev";
                 "concat";
                 "enumTo"]
    ~examples:(List.map ~f:example 
               [[1;2;3];
                [4;2]]);;*)

(*(* Try to generate multfirst -- no way, there is no head *)
let free_lib = Library.create ();;
let multfirst_test =
    let example xs = (([list_to_natlist xs],["Nat"]), list_to_natlist (List.map ~f:(fun _ -> List.hd_exn xs) xs)) in
  test_enumeration
    ~msg:"Generate multfirst"
    (parse_type "@ List #0 -> List #0")
    free_lib
    1
    ~components:[
                 "curry";
                 "uncurry";
                 "nil";
                 "con";
                 "zero";
                 "succ";
                 "true";
                 "false";
                 "pair";
                 "fst";
                 "snd";
                 "map";
                 "foldr";
                 "foldl";
                 "range";
                 "foldNat";
                 "natEq";
                 "natGeq";
                 "sub";
                 "add";
                 "length";
                 "replicate";
                 "append";
                 "rev";
                 "concat";
                 "enumTo"]
    ~examples:(List.map ~f:example 
               [[1;2;3];
                [4;2]]);;*)

  


