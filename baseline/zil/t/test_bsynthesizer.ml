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
(* Plain enumeration *)


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
let test_enumeration ?debug:(debug=true) ?msg:(msg="Basic enumeration") goal_type free_lib ?examples:(examples=[]) ?components:(components=[]) nof_programs =

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

  (* TODO debugging *) let () = if debug then printf "\n\n\n%s...\n" msg else () in (* end *)

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
   let satisfying = Synthesiser.enumerate_satisfying ~debug queue ~sym_lib:sym_lib_comp ~free_lib:free_lib ~sym_def:sym_def ~examples:examples nof_programs in
   (*let closed = (Synthesiser.enumerate queue sym_lib_uni free_lib nof_programs) in
   let satisfying = Synthesiser.filter_satisfying closed examples ~sym_def:(Library.get_lib_def sym_lib) in
   let () = print_string (sprintf "\n***Closed***\n________________\n%s\n" (String.concat ~sep:"\n" (List.map ~f:Program.to_string closed))) in*)
   let () = if debug then printf "\n***Satisfying***\n________________\n%s\n" (String.concat ~sep:"\n" (List.map ~f:Program.to_string satisfying)) else () in
   satisfying


(******************************************************************************)
(* Start enumeration from given template *)
let test_hypothesis1 ?debug:(debug=true) ?msg:(msg="First order enumeration") goal_type (holes, template) ?examples:(examples=[]) ?components:(components=[]) nof_programs =
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

  (* TODO debugging *) let () = if debug then printf "\n\n\n%s...\n" msg else () in (* end *)


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
  let satisfying = Synthesiser.enumerate_satisfying ~debug queue ~sym_lib:sym_lib_comp ~free_lib:free_lib ~sym_def:sym_def ~examples:examples nof_programs in
  let () = if debug then printf "\n***Satisfying***\n________________\n%s\n" (String.concat ~sep:"\n" (List.map ~f:Program.to_string satisfying)) else () in
  satisfying


(******************************************************************************)
(* Test black_list pruning *)
let test_black_list ?debug:(debug=true) ?msg:(msg="Basic enumeration") goal_type free_lib ~black_list ?examples:(examples=[]) ?components:(components=[]) nof_programs =

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

  (* TODO debugging *) let () = if debug then printf "\n\n\n%s...\n" msg else () in (* end *)

  let prog = Program.reset first_prog (transform_type free_lib goal_type) in
  let queue = Heap.create ~min_size:100 ~cmp:Program.compare () in
  let () = Heap.add queue prog in

(*(* TODO debugging *) let () = print_string "Printing free_lib...\n" in
   let () = print_free_lib free_lib in
   let () = print_string "\n________________\n" in
   let () = print_string "Printing sym_lib_uni...\n" in
   let () = print_sym_lib sym_lib_uni in
   let () = print_string "\n________________\n\n" in (* end *)*)
   let black_set = String.Set.of_list black_list in
   let () = if debug then 
     (let () = String.Set.iter ~f:print_endline black_set in
      print_endline "\n\n___________\n")
     else () in


   let examples =
     List.map
       ~f:(fun (input, output) -> (instantiate_free input, eval ~sym_def:sym_def (parse_term output)))
       examples in
   let satisfying = Synthesiser.enumerate_with_black_list ~debug queue ~sym_lib:sym_lib_comp ~free_lib:free_lib ~sym_def:sym_def ~black_list:(List.map ~f:parse_term black_list) ~examples:examples nof_programs in
   (*let closed = (Synthesiser.enumerate queue sym_lib_uni free_lib nof_programs) in
   let satisfying = Synthesiser.filter_satisfying closed examples ~sym_def:(Library.get_lib_def sym_lib) in
   let () = print_string (sprintf "\n***Closed***\n________________\n%s\n" (String.concat ~sep:"\n" (List.map ~f:Program.to_string closed))) in*)
   let () = if debug then printf "\n***Satisfying***\n________________\n%s\n" (String.concat ~sep:"\n" (List.map ~f:Program.to_string satisfying))  else () in
   satisfying

(******************************************************************************)
(* Best manual black list for now *)
let black_list = [
    "append ^0 (nil ^0)";
    "append ^0 ?0 (nil ^0)";
    "b_add ?0 b_zero";
    "b_add b_zero";
    "b_div ?0 b_zero";
    "b_div ?0 (b_succ b_zero)";
    "b_div b_zero";
    "b_div (b_succ b_zero)";
    "b_foldNat ^0 ?0 ?0 b_zero";
    "b_foldNat ^0 b_succ b_zero";
    "b_foldNatNat ^0 (b_foldNatNat ^0 ?0 ?0 ?0)";
    "b_foldNatNat ^0 ?0 ?0 b_zero";
    "b_is_zero b_zero";
    "b_max b_zero b_zero";
    "b_mul (b_succ b_zero)";
    "b_mul ?0 (b_succ b_zero)";
    "b_mul ?0 b_zero";
    "b_mul b_zero";
    "b_sub ?0 b_zero";
    "b_sub b_zero";
    "concat ^0 (nil ^0)";
    "const ^0 ^0 ?0 ?0";
    "enumFromTo (b_succ b_zero)";
    "enumTo b_zero";
    "enumTo (prod ?0 ?0)";
    "flip ^0 ^0 ^0 ?0 ?0 ?0";
    "foldl ^0 ^0 ?0 ?0 (nil ^0)";
    "foldr ^0 ^0 (con ^0) (nil ^0)";
    "foldr ^0 ^0 ?0 ?0 (nil ^0)";
    "fst ^0 ^0 (pair ^0 ^0 ?0 ?0)";
    "head ^0 (con ^0 ?0 ?0)";
    "head ^0 (enumFromTo ?0 ?0)";
    "head ^0 (enumTo ?0)";
    (*"head ^0 (map ^0 ^0 ?0 ?0)";*)
    "head ^0 (nil ^0)";
    "is_nil ^0 (nil ^0)";
    (*"length ^0 (con ^0 ?0 ?0)";*)
    "length ^0 (enumFromTo ?0 ?0)";
    "length ^0 (enumTo ?0)";
    "length ^0 (map ^0 ^0 ?0 ?0)";
    "length ^0 (nil ^0)";
    "length ^0 (rev ^0 ?0)";
    "map ^0 ^0 ?0 (nil ^0)";
    "not (not ?0)";
    "prod (con ^0 ?0 (nil))";
    "prod (con ^0 b_zero ?0)";
    "prod (nil ^0)";
    "prod (rev ^0 ?0)";
    "replicate ^0 b_zero";
    "rev ^0 (con ^0 ?0 (nil ^0))";
    "rev ^0 (map ^0 ^0 ?0 (rev ^0 ?0))";
    "rev ^0 (nil ^0)";
    "rev ^0 (rev ^0 ?0)";
    "snd ^0 ^0 (pair ^0 ^0 ?0 ?0)";
    "sum (con ^0 ?0 (nil ^0))";
    "sum (nil ^0)";
    "sum (rev ^0 ?0)";
    "tail ^0 (con ^0 ?0 (nil))";
    "tail ^0 (enumFromTo ?0 ?0)";
    "tail ^0 (nil ^0)";
    "uncurry ^0 ^0 ^0 ?0 (pair ^0 ^0 ?0 ?0)";
];;


(******************************************************************************)
(* Automatic black_list generation for id-pruning *)
let generate_id_blacklist ?components:(components=[]) n =
  let examples a =
    let constructors = [
      "con";
      "nil";
      "b_succ";
      "b_zero";
    ] in
    let inputs = test_enumeration ~debug:false a (Library.create ()) ~components:constructors 8 in
    List.map
      ~f:(fun input -> (([Program.to_string input],[]), Program.to_string input))
      inputs in
  let template a =
    let (a1, first_prog) = Program.get_fresh_type_hol first_prog in
    ([Type.to_string (Type.Arr (a1,a)); Type.to_string a1],
     "?1 ?2") in
  let type_list = List.map ~f:parse_type ["Int"; "List Int"; "List (List Int)"] in
  let id_list =
    List.map
      ~f:(fun a -> test_hypothesis1 ~debug:false (Type.Arr (a, a)) (template a) ~components ~examples:(examples a) n)
      type_list in
  let id_list = List.concat id_list in
  List.map ~f:(fun prog -> to_string_ignore_types (Program.to_term prog)) id_list


let test_id_pruning ?debug:(debug=true) ?msg:(msg="With id-pruning") goal_type ~black_list ?examples:(examples=[]) ?components:(components=[]) nof_programs nof_id =
  let free_lib = Library.create () in
  test_black_list ~debug ~msg:msg goal_type free_lib ~black_list:(List.append black_list (generate_id_blacklist ~components nof_id)) ~examples:examples ~components:components nof_programs


(******************************************************************************)
(* Enumeration with templates *)
let test_enumeration_with_templates ?debug:(debug=true) ?msg:(msg="Enumeration with templates and black list") goal_type free_lib ~black_list ?examples:(examples=[]) ?ho_components:(ho_components=[]) ?fo_components:(fo_components=[]) ~nof_hoc ~nof_hol ~nof_cal =

  let sym_lib_comp components = (match components with
    | [] -> sym_lib_uni
    | _ -> (let sym_lib_comp_aux = Library.create () in
            let () = Library.iter_types
              (fun i a k -> Library.add_type i a k sym_lib_comp_aux)
              sym_lib_uni in
            let () = List.iter
              ~f:(fun i -> let (m, a, args) = Library.lookup_term sym_lib_uni i in
                        Library.add_term i m a ~typ_args:args sym_lib_comp_aux)
              components in
            sym_lib_comp_aux)) in

  (* TODO debugging *) let () = if debug then printf "\n\n\n%s...\n" msg else () in (* end *)

  (*let compare (prog1, n1) (prog2, n2) = match Program.compare prog1 prog2 with
    | 0 -> n2 - n1
    | n -> n in*)
  let compare (prog1, n1) (prog2,n2) =
    let cost (prog, n) = Program.nof_holes prog - n in
    (- cost (prog2, n2) + cost (prog1, n1)) in

  let prog = Program.reset first_prog (transform_type free_lib goal_type) in
  let queue = Heap.create ~min_size:100 ~cmp:compare () in
  let () = Heap.add queue (prog,0) in

  let black_set = String.Set.of_list black_list in
  let () = if debug then 
    (let () = String.Set.iter ~f:print_endline black_set in
     print_endline "\n\n___________\n")
    else () in

    let examples =
      List.map
        ~f:(fun (input, output) -> (instantiate_free input, eval ~sym_def:sym_def (parse_term output)))
        examples in
    let satisfying =
      Synthesiser.enumerate_with_templates
        ~debug
        queue
        ~higher_order_lib:(sym_lib_comp ho_components)
        ~first_order_lib:(sym_lib_comp fo_components)
        ~free_lib:free_lib
        ~sym_def:sym_def
        ~black_list:(List.map ~f:parse_term black_list)
        ~examples
        ~nof_hoc
        ~nof_hol
        ~nof_cal in
    let () = if debug then (printf "\n***Satisfying***\n________________\n%s\n" 
      (match satisfying with
      | None -> "No program found"
      | Some prog -> (Program.to_string prog)))  else () in
   satisfying

(******************************************************************************)
(* Generate blacklist *)
(*let blacklist = generate_id_blacklist 100;;
let blackset = String.Set.of_list blacklist;;
let () = String.Set.iter
  ~f:(fun s -> print_endline s)
  blackset;;*)


(*(* Generate programs *)

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
                  7]);;*)

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


(*(* Try to generate droplast *)
let free_lib = Library.create ();;
let droplast_test =
  let droplast xs = List.take xs ((List.length xs) - 1) in

  let example xs = (([list_to_intlist xs],["Int"]),  (list_to_intlist (droplast xs))) in
  test_enumeration
    ~msg:"Generate droplast"
    (parse_type "List Int -> List Int")
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
                 [[1;2;3];
                  [4;2]]);;*)

(*(* Try to generate take *)
let free_lib = Library.create ();;
let take_test =
    let example (n, xs) = (([string_of_int n; list_to_intlist xs],["Int"]),  (list_to_intlist (List.take xs n))) in
  test_enumeration
    ~msg:"Generate take"
    (parse_type "@ Int -> List #0 -> List #0")
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
                 [(1, [1;2;3]);
                  (2, [4;2]);
                  (2, [1;4;2])]);;*)

(*(* Try to generate the identity function (most general form) *)
let free_lib = Library.create ();;
let id_test =
    let example n = (([string_of_int n],["Int"]),  string_of_int n) in
  test_enumeration
    ~msg:"Generate general id"
    (parse_type "@ #0 -> #0")
    free_lib
    100
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
                 [1;
                  3]);;*)


(*(* Try to generate the identity function (on lists) *)
let free_lib = Library.create ();;
let id_test =
    let example xs = (([list_to_intlist xs],["Int"]),  list_to_intlist xs) in
  test_enumeration
    ~msg:"Generate id on lists"
    (parse_type "@ List #0 -> List #0")
    free_lib
    100
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
                 [[1];
                  [1;2;3]]);;*)


(*(* Try to generate the identity function (on integers) *)
let free_lib = Library.create ();;
let id_test =
    let example n = (([string_of_int n],[]),  string_of_int n) in
  test_enumeration
    ~msg:"Generate integer id"
    (parse_type "Int -> Int")
    free_lib
    100
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
                 [1;
                  3;
                  4]);;*)

(*(* Try to generate enumTo. with a very simple blacklist *)
let black_list = ["head (nil)"; "tail (nil)"; "append (nil)"];;
let free_lib = Library.create ();;
let enumTo_test =
  let example n = (([string_of_int n],[]),  list_to_intlist (List.range ~stop:`inclusive 1 n)) in
  test_black_list
    ~msg:"Generate enumTo"
    (parse_type "Int -> List Int")
    free_lib
    ~black_list:black_list
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
                 (*"enumTo";*)
                 "enumFromTo"
                ]
    ~examples:(List.map ~f:example
                 [1;
                  3]);;*)

(*(* Try to generate replicate. with a very simple blacklist *)
let black_list = ["head (nil)"; "tail (nil)"; "append (nil)"; "append _ (nil)"];;
(*let black_list = [];;*)
let free_lib = Library.create ();;
let replicate_test =
    let replicate n x =
      let rec repl_aux n = match n with
      | 0 -> []
      | n when n > 0 -> x::(repl_aux (n-1))
      | _ -> invalid_arg "first argument to replicate must be non-negative"
    in repl_aux n in

    let example (n, x) = (([string_of_int n; string_of_int x],["Int"]),  list_to_intlist (replicate n x)) in
  test_black_list
    ~msg:"Generate replicate"
    (parse_type "@ Int -> #0 -> List #0")
    free_lib
    ~black_list:black_list
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
                 (*"replicate";*)
                 "append";
                 "rev";
                 "concat";
                 "enumTo";
                 "enumFromTo"
                ]
    ~examples:(List.map ~f:example
                 [(1,0);
                  (3,2)]);;*)

(*(* Try to generate map_add. with a very simple blacklist *)
let black_list = [
    "undefined";
    "head (nil)";
    "tail (nil)";
    "append (nil)";
    "append _ (nil)";
    "const _ _";
    ];;
(*let black_list = [];;*)
let free_lib = Library.create ();;
let map_add_test =
    let example (n, xs) = (([string_of_int n; list_to_intlist xs],[]),  list_to_intlist (List.map ~f:(fun x -> x + n) xs)) in
  test_black_list
    ~msg:"Generate map_add"
    (parse_type "Int -> List Int -> List Int")
    free_lib
    ~black_list:black_list
    1
    ~components:[
                 "const";
                 "flip";
                 "curry";
                 "uncurry";
                 "fanout";
                 "ignore";
                 "undefined";
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
                 [(1,[0]);
                  (3,[1;2])]);;*)

(*(* Try to generate concat. with a very simple blacklist *)
(*let black_list = [
    (*"undefined";*)
    "head (nil)";
    "tail (nil)";
    "append (nil)";
    "append _ (nil)";
    "const _ _";
    "fst (pair _ _)";
    "snd (pair _ _)";
    "head (con _ _)";
    "concat (nil)";
    "b_add b_zero";
    "b_add _ b_zero";
    "b_sub b_zero";
    "b_sub _ b_zero";
    "b_mul (succ b_zero)";
    "b_mul (prod (nil))";
    "b_mul _ (succ b_zero)";
    "b_mul _ (prod (nil))";
    "b_succ (b_sub _ (prod (nil)))";
    "b_add _ (length (nil))";
    ];;*)
let free_lib = Library.create ();;
let concat_test =
    let example xss = (([list_to_list "(List Int)" list_to_intlist xss],["Int"]),  list_to_intlist (List.concat xss)) in
  test_black_list
    ~msg:"Generate concat"
    (*~debug:false*)
    (parse_type "@ List (List #0) -> List #0")
    free_lib
    ~black_list:black_list
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
                 (*"concat";*)
                 "enumTo";
                 "enumFromTo"
                ]
    ~examples:(List.map ~f:example
                 [[[2;3];[]];
                  [[1];[2;3]]]);;*)

(*(* Try to generate enumFromTo. with a longer black_list *)
(*let black_list = [
    (*"head (nil)";
    "tail (nil)";
    "append (nil)";
    "append (rev (nil))";
    "append _ (nil)"; (* not sure this pattern does something *)
    "const _ _";
    "fst (pair _ _)";
    "snd (pair _ _)";
    "head (con _ _)";
    "concat (nil)";*)
    "b_add b_zero";
    "b_add _ b_zero";
    "b_sub b_zero";
    "b_sub _ b_zero";
    "b_mul (succ b_zero)";
    (*"b_mul (prod (nil))";*)
    "b_mul _ (succ b_zero)";
    "b_foldNatNat (b_foldNatNat _ _ _)";
    "b_foldNatNat (b_foldNatNat _)";
    "b_foldNatNat (b_foldNatNat)";
    "b_foldNatNat (b_foldNatNat _ _)";
    (*"b_mul _ (prod (nil))";
    "b_succ (b_sub _ (prod (nil)))";
    "b_add _ (length (nil))"*)
    ];;*)
let free_lib = Library.create ();;
let enumFromTo_test =
    let example (n, m) = (([string_of_int n; string_of_int m],[]),  list_to_intlist (List.range ~stop:`inclusive n m)) in
  test_black_list
    ~msg:"Generate enumFromTo"
    (*~debug:false*)
    (parse_type "Int -> Int -> List Int")
    free_lib
    ~black_list:black_list
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
                 (*"enumFromTo"*)
                ]
    ~examples:(List.map ~f:example
                 [(1,3);
                  (2,5)]);;*)

(*(* Try to generate enumFromTo. with a very long black_list *)
let enumFromTo_test =
    let example (n, m) = (([string_of_int n; string_of_int m],[]),  list_to_intlist (List.range ~stop:`inclusive n m)) in
  test_id_pruning
    ~msg:"Generate enumFromTo"
    (parse_type "Int -> Int -> List Int")
    ~black_list:black_list
    1
    100
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
                 (*"pair";
                 "fst";
                 "snd";*)
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
                 (*"enumFromTo"*)
                ]
    ~examples:(List.map ~f:example
                 [(1,3);
                  (2,5)]);;*)

(*(* Try to generate maximum with an accurate manual black_list *)
let maximum_test =
    let example xs = (([list_to_intlist xs],[]),  string_of_int (match List.max_elt ~cmp:compare xs with Some m -> m | None -> invalid_arg "empty list")) in
  test_black_list
    ~msg:"Generate maximum"
    (parse_type "List Int -> Int")
    ~black_list:black_list
    (Library.create ())
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
                 [[2;4;3];
                  [5;1];
                  [2;1;1]]);;*)


(*(* Try to generate concat. with a very simple blacklist *)
let free_lib = Library.create ();;
let concat_test =
  let example xss = (([list_to_list "(List Int)" list_to_intlist xss],["Int"]),  list_to_intlist (List.concat xss)) in
  test_enumeration_with_templates
    ~msg:"Generate concat"
    (*~debug:false*)
    (parse_type "@ List (List #0) -> List #0")
    free_lib
    ~black_list:black_list
    ~nof_hoc:2
    ~nof_hol:5
    ~nof_cal:10
    ~ho_components:[
                 (*"const";*)
                 (*"flip";
                 "curry";
                 "uncurry";
                 "fanout";
                 "ignore";*)
                 (*"undefined";*)
                 (*"nil";*)
                 (*"con";
                 "head";
                 "tail";
                 (*"true";*)
                 (*"false";*)
                 "pair";
                 "fst";
                 "snd";*)
                 "map";
                 "foldr";
                 "foldl";
                 (*"sum";
                 "prod";
                 (*"b_zero";*)
                 "b_succ";*)
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
                 (*"concat";*)
                 "enumTo";
                 "enumFromTo"
                ]
    ~fo_components:[
                 "const";
                 "nil";
                 "con";
                 "head";
                 "tail";
                 "true";
                 "false";
                 "pair";
                 "fst";
                 "snd";
                 "sum";
                 "prod";
                 "b_zero";
                 "b_succ";
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
                 (*"concat";*)
                 "enumTo";
                 "enumFromTo"
                ]
    ~examples:(List.map ~f:example
                 [[[1;2;3];[4;5]];
                  [[1];[2;3]]]);;*)


(*(* Try to generate sum with an accurate manual black_list *)
let sum_test =
    let example xs = (([list_to_intlist xs],[]),  string_of_int (List.fold_left ~f:(+) ~init:0 xs)) in
  test_black_list
    ~msg:"Generate sum"
    (parse_type "List Int -> Int")
    ~black_list:black_list
    (Library.create ())
    1
    ~components:[
                 (*"const";
                 "flip";
                 "curry";
                 "uncurry";
                 "fanout";
                 "ignore";*)
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
                 (*"sum";*)
                 "prod";
                 "b_zero";
                 "b_succ";
                 (*"b_foldNat";*)
                 (*"b_foldNatNat";*)
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
                 [[2;5];
                  [4;2;1]]);;*)

(*(* Try to generate filter is_zero with an accurate manual black_list *)
let filter_is_zero_test =
    let example xs = (([list_to_intlist xs],[]), list_to_intlist (List.filter ~f:(fun x -> x = 0) xs)) in
  test_black_list
    ~msg:"Generate filter is_zero"
    (parse_type "List Int -> List Int")
    ~black_list:black_list
    (Library.create ())
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
                 "filter";
                 "sum";
                 "prod";
                 "b_zero";
                 "b_succ";
                 "b_is_zero";
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
                 [[2;5;0];
                  [4;0;2;1];
                  [0;0;1]]);;*)

(*(* Try to generate member with an accurate manual black_list *)
let member_test =
    let example (x, xs) = (([string_of_int x; list_to_intlist xs],[]), string_of_bool (List.mem xs x)) in
  test_black_list
    ~msg:"Generate member"
    (parse_type "Int -> List Int -> Bool")
    ~black_list:black_list
    (Library.create ())
    1
    ~components:[
                 (*"const";
                 "flip";
                 "curry";
                 "uncurry";
                 "fanout";
                 "ignore";*)
                 (*"undefined";*)
                 "nil";
                 "con";
                 "head";
                 "tail";
                 "is_nil";
                 "true";
                 "false";
                 "not";
                 "pair";
                 "fst";
                 "snd";
                 "map";
                 "foldr";
                 "foldl";
                 "filter";
                 (*"sum";
                 "prod";*)
                 "b_zero";
                 "b_succ";
                 "b_is_zero";
                 "b_foldNat";
                 "b_foldNatNat";
                 "b_add";
                 "b_sub";
                 "b_mul";
                 "b_div";
                 "b_max";
                 "b_eq";
                 (*"b_neq";
                 "b_leq";
                 "b_geq";*)
                 (*"length";*)
                 (*"factorial";*)
                 "replicate";
                 "append";
                 "rev";
                 "concat";
                 (*"enumTo";*)
                 (*"enumFromTo"*)
                ]
    ~examples:(List.map ~f:example
                 [(5, [1;2;3]);
                  (1, [1;2;3]);
                  (2, [4;1;3;5]);
                  (4, [3;1;4;5]);
                  (1, [0])]);;*)

(*(* Try to generate dedup with an accurate manual black_list -- not possible *)
let dedup_test =
    let example xs = (([list_to_intlist xs],[]), list_to_intlist (List.dedup xs)) in
  test_black_list
    ~msg:"Generate dedup"
    (parse_type "List Int -> List Int")
    ~black_list:black_list
    (Library.create ())
    1
    ~components:[
                 (*"const";
                 "flip";
                 "curry";
                 "uncurry";
                 "fanout";
                 "ignore";*)
                 (*"undefined";*)
                 "nil";
                 "con";
                 "head";
                 "tail";
                 "is_nil";
                 (*"true";
                 "false";*)
                 "not";
                 (*"pair";
                 "fst";
                 "snd";*)
                 "map";
                 "foldr";
                 "foldl";
                 "filter";
                 (*"sum";
                 "prod";*)
                 (*"b_zero";
                 "b_succ";
                 "b_is_zero";
                 "b_foldNat";
                 "b_foldNatNat";
                 "b_add";
                 "b_sub";
                 "b_mul";
                 "b_div";
                 "b_max";*)
                 "b_eq";
                 (*"b_neq";
                 "b_leq";
                 "b_geq";*)
                 (*"length";*)
                 (*"factorial";*)
                 (*"replicate";
                 "append";
                 "rev";
                 "concat";*)
                 (*"enumTo";*)
                 (*"enumFromTo";*)
                 "member"
                ]
    ~examples:(List.map ~f:example
                 [[1;2;3];
                  [1;1];
                  [1;2;1]]);;*)


(*(* Try to generate dropmax with an accurate manual black_list *)
let dropmax_test =
    let example xs = (([list_to_intlist xs],[]), list_to_intlist (List.filter ~f:(fun x -> x = (match (List.max_elt ~cmp:compare xs) with Some m -> m | None -> invalid_arg "max of empty list")) xs)) in
  test_black_list
    ~msg:"Generate dropmax"
    (parse_type "List Int -> List Int")
    ~black_list:black_list
    (Library.create ())
    1
    ~components:[
                 (*"const";
                 "flip";
                 "curry";
                 "uncurry";
                 "fanout";
                 "ignore";*)
                 (*"undefined";*)
                 "nil";
                 "con";
                 "head";
                 "tail";
                 "is_nil";
                 (*"true";
                 "false";*)
                 "not";
                 (*"pair";
                 "fst";
                 "snd";*)
                 "map";
                 "foldr";
                 "foldl";
                 "filter";
                 (*"sum";
                 "prod";*)
                 "b_zero";
                 "b_succ";
                 (*"b_is_zero";
                 "b_foldNat";
                 "b_foldNatNat";
                 "b_add";
                 "b_sub";
                 "b_mul";
                 "b_div";*)
                 "b_max";
                 "b_eq";
                 (*"b_neq";*)
                 (*"b_leq";
                 "b_geq";*)
                 (*"length";*)
                 (*"factorial";*)
                 (*"replicate";
                 "append";
                 "rev";
                 "concat";*)
                 (*"enumTo";*)
                 (*"enumFromTo";*)
                 (*"member"*)
                ]
    ~examples:(List.map ~f:example
                 [[1;2;3];
                  [1;1];
                  [1;2;1]]);;*)

(*(* Try to generate map_double with an accurate manual black_list *)
let map_double_test =
    let example xs = (([list_to_intlist xs],[]), list_to_intlist (List.map ~f:(fun x -> x * 2) xs)) in
  test_black_list
    ~msg:"Generate map_double"
    (parse_type "List Int -> List Int")
    ~black_list:black_list
    (Library.create ())
    1
    ~components:[
                 (*"const";
                 "flip";
                 "curry";
                 "uncurry";
                 "fanout";
                 "ignore";*)
                 (*"undefined";*)
                 "nil";
                 "con";
                 "head";
                 "tail";
                 "is_nil";
                 (*"true";
                 "false";*)
                 "not";
                 (*"pair";
                 "fst";
                 "snd";*)
                 "map";
                 "foldr";
                 "foldl";
                 "filter";
                 "sum";
                 "prod";
                 "b_zero";
                 "b_succ";
                 "b_is_zero";
                 "b_foldNat";
                 "b_foldNatNat";
                 "b_add";
                 "b_sub";
                 "b_mul";
                 "b_div";
                 "b_max";
                 "b_eq";
                 (*"b_neq";*)
                 (*"b_leq";
                 "b_geq";*)
                 "length";
                 (*"factorial";*)
                 "replicate";
                 "append";
                 "rev";
                 "concat";
                 "enumTo";
                 "enumFromTo";
                 (*"member"*)
                ]
    ~examples:(List.map ~f:example
                 [[1;2;3];
                  [1;1];
                  [1;2;1]]);;*)


