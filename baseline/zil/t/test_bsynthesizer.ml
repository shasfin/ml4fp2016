open TestSimple;;
open Printf;;
open Core.Std;;

open Zil.Lambda;;
open Zil.Parse;;
open Zil;;


(******************************************************************************)
(* Define library *)

let sym_lib = Library.read_from_file "src/b_library.tm";;
let sym_def = Library.get_lib_def sym_lib;;

(******************************************************************************)
(* Syntax sugar *)

(* Convert [a;b;c] to con A (f a) (con A (f b) (con A (f c) (nil A))) *)
let rec list_to_list a f xs = match xs with
  | [] -> sprintf "nil %s" a
  | x::xs -> sprintf "con %s (%s) (%s)" a (f x) (list_to_list a f xs)

(* Convert [1;2;3] to a list of nat *)
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


(******************************************************************************)
(* Generate programs *)

(* Try to generate factorial *)
let free_lib = Library.create ();;
let factorial_test =
  let rec factorial = function
    | 0 | 1 -> 1
    | n when n > 1 -> n * (factorial (n-1))
    | _ -> invalid_arg "Argument to factorial must be positive" in

  let example x = (([string_of_int x],[]), string_of_int (factorial x)) in
  test_enumeration
    ~msg:"Generate factorial"
    (parse_type "Int -> Int")
    free_lib
    1
    ~components:[
                 "const";
                 "flip";
                 "curry";
                 "uncurry";
                 "fanout";
                 "ignore";
                 (*"undefined";*)
                 "nil";
                 "con";
                 "head";
                 "tail";
                 "true";
                 "false";
                 "pair";
                 "fst";
                 "snd";
                 "map";
                 "foldr";
                 "foldl";
                 "sum";
                 "prod";
                 "b_zero";
                 "b_succ";
                 "b_foldNat";
                 "b_foldNatNat";
                 "b_add";
                 "b_sub";
                 "b_mul";
                 "b_div";
                 "b_max";
                 "length";
                 (*"factorial";*)
                 "replicate";
                 "append";
                 "rev";
                 "concat";
                 "enumTo";
                 "enumFromTo"
                ]
    ~examples:(List.map ~f:example
                 [2;
                  7]);;

(*(* Try to generate enumFromTo *)
let enumFromTo_test =
    let example (x, y) = (([string_of_int x; string_of_int y],[]), list_to_intlist (List.range ~stop:`inclusive x y)) in
  test_hypothesis1
    ~msg:"Generate enumFromTo"
    (parse_type "Int -> Int -> List Int")
    (["Int";
      "Int"],
     "map Int Int (b_add ?1) (enumTo ?2)")
    1
    ~components:[
                 "b_add";
                 "b_sub";
                 "b_zero";
                 "b_succ";
                ]
    ~examples:(List.map ~f:example
                 [(2,5);
                  (1,2);
                  (1,3)]);;*)


(*(* Try to generate enumTo *)
let free_lib = Library.create ();;
let enumFromTo_test =
    let example x = (([string_of_int x],[]), list_to_intlist (List.range ~stop:`inclusive 1 x)) in
  test_enumeration
    ~msg:"Generate enumTo"
    (parse_type "Int -> List Int")
    free_lib
    1
    ~components:[
                 "const";
                 "flip";
                 "curry";
                 "uncurry";
                 "fanout";
                 "ignore";
                 (*"undefined";*)
                 "nil";
                 "con";
                 "head";
                 "tail";
                 "true";
                 "false";
                 "pair";
                 "fst";
                 "snd";
                 "map";
                 "foldr";
                 "foldl";
                 "sum";
                 "prod";
                 "b_zero";
                 "b_succ";
                 "b_foldNat";
                 "b_foldNatNat";
                 "b_add";
                 "b_sub";
                 "b_mul";
                 "b_div";
                 "b_max";
                 "length";
                 "factorial";
                 "replicate";
                 "append";
                 "rev";
                 "concat";
                 (*"enumTo";*)
                 (*"enumFromTo"*)
                ]
    ~examples:(List.map ~f:example
                 [2;
                  4]);;*)

(*(* Try to generate replicate *)
let free_lib = Library.create ();;
let replicate_test =
  let example (x, n) = 
    let rec replicate n = match n with
      | 0 -> []
      | n -> x::(replicate (n-1)) in
      
      (([string_of_int x; string_of_int n],["Int"]), list_to_intlist (replicate n)) in
  test_enumeration
    ~msg:"Generate replicate"
    (parse_type "@ #0 -> Int -> List #0")
    free_lib
    1
    ~components:[
                 "const";
                 "flip";
                 "curry";
                 "uncurry";
                 "fanout";
                 "ignore";
                 (*"undefined";*)
                 "nil";
                 "con";
                 "head";
                 "tail";
                 "true";
                 "false";
                 "pair";
                 "fst";
                 "snd";
                 "map";
                 "foldr";
                 "foldl";
                 "sum";
                 "prod";
                 "b_zero";
                 "b_succ";
                 "b_foldNat";
                 "b_foldNatNat";
                 "b_add";
                 "b_sub";
                 "b_mul";
                 (*"b_div";*)
                 "b_max";
                 "length";
                 "factorial";
                 (*"replicate";*)
                 "append";
                 "rev";
                 "concat";
                 "enumTo";
                 "enumFromTo"
    ]    
    ~examples:(List.map ~f:example
               [(1,0);
                (0,2);
                (3,1)]);;*)



