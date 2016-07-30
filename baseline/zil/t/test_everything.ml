open Printf;;
open Core.Std;;

open Zil.Lambda;;
open Zil.Parse;;
open Zil.Benchmark;;
open Zil;;


(* Read library *)
let sym_lib = Library.read_from_file "src/b_library.tm";;
let sym_def = Library.get_lib_def sym_lib;;

(* Prepare library for unification *)
let first_prog = Program.create ();;
let (sym_lib_uni, first_prog) = Synthesiser.prepare_lib sym_lib first_prog;;


let components = [
  "const";
  "flip";
  (*"curry";
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
  "b_neq";
  (*"b_leq";
  "b_geq";*)
  "length";
  (*"factorial";*)
  "replicate";
  "append";
  "reverse";
  "concat";
  "enumTo";
  "enumFromTo";
  "member";
  "maximum"
]

(* Utility function to recognize higher-order types *)
let rec is_first_order_type a = match a with
    | Type.All b -> false (* assume no universal types should be present *)
    | Type.Arr (a, b) -> (match a with
      | Type.All b -> false (* assume no universal types should be present *)
      | Type.Arr (a, b) -> false
      | _ -> is_first_order_type b)
    | _ -> true


(* Partition components into higher-order and first-order *)
let (fo_components, ho_components) = List.partition_tf
  ~f:(fun c -> is_first_order_type (Library.lookup_term_sig sym_lib_uni c))
  components


let black_list = List.map ~f:parse_term
[
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
  "enumTo (prod ?0)";
  "flip ^0 ^0 ^0 ?0 ?0 ?0";
  "foldl ^0 ^0 ?0 ?0 (nil ^0)";
  "foldr ^0 ^0 (con ^0) (nil ^0)";
  "foldr ^0 ^0 ?0 ?0 (nil ^0)";
  (*"fst ^0 ^0 (pair ^0 ^0 ?0 ?0)";*)
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
  "length ^0 (reverse ^0 ?0)";
  "map ^0 ^0 ?0 (nil ^0)";
  "not (not ?0)";
  "prod (con ^0 ?0 (nil))";
  "prod (con ^0 b_zero ?0)";
  "prod (nil ^0)";
  "prod (reverse ^0 ?0)";
  "replicate ^0 b_zero";
  "reverse ^0 (con ^0 ?0 (nil ^0))";
  "reverse ^0 (map ^0 ^0 ?0 (reverse ^0 ?0))";
  "reverse ^0 (nil ^0)";
  "reverse ^0 (reverse ^0 ?0)";
  (*"snd ^0 ^0 (pair ^0 ^0 ?0 ?0)";*)
  "sum (con ^0 ?0 (nil ^0))";
  "sum (nil ^0)";
  "sum (reverse ^0 ?0)";
  "tail ^0 (con ^0 ?0 (nil))";
  "tail ^0 (enumFromTo ?0 ?0)";
  "tail ^0 (nil ^0)";
  (*"uncurry ^0 ^0 ^0 ?0 (pair ^0 ^0 ?0 ?0)";*)
]

let benchmarks = [
  (*Benchmark.append;
  Benchmark.concat;
  Benchmark.droplast;
  Benchmark.dropmax;
  Benchmark.enumFromTo;
  Benchmark.enumTo;
  Benchmark.factorial;
  Benchmark.last;*)
  Benchmark.length;
  (*Benchmark.map_add;
  Benchmark.map_double;
  Benchmark.maximum;
  Benchmark.member;
  Benchmark.multfirst;
  Benchmark.multlast;
  Benchmark.replicate;
  Benchmark.reverse;
  Benchmark.stutter;
  Benchmark.sum;*)
]


let max_lines = 10000000

let test ~sym_lib_uni ~first_prog ~sym_def benchmark =

  (* Use only 'components' for generation, don't add those that have the same name as the benchmark *)
  let compute_sym_lib_comp components =
    let components = (List.filter ~f:(fun c -> not (c = benchmark.name)) components)in
    let nof_components = List.length components in
    (match components with
    | [] -> (let tot_nof_components =
        Library.fold_terms
          (fun i m a args acc -> acc + 1)
          sym_lib_uni
          0 in
        (tot_nof_components, sym_lib_uni))
    | _ -> (let sym_lib_comp = Library.create () in
            let () = Library.iter_types
              (fun i a k -> Library.add_type i a k sym_lib_comp)
              sym_lib_uni in
            let () = List.iter
              ~f:(fun i -> let (m, a, args) = Library.lookup_term sym_lib_uni i in
                        Library.add_term i m a ~typ_args:args sym_lib_comp)
              components in
            (nof_components, sym_lib_comp))) in

  let (nof_components, sym_lib_comp) = compute_sym_lib_comp components in


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

    dearrowise (deuniversalise a 0) 0 in

  (* Prepare type and example for synthesis *)
  let free_lib = Library.create () in
  let goal_type = transform_type free_lib benchmark.goal_type in
  let examples =
     (List.map
       ~f:(fun (input, output) -> (SyntaxSugar.instantiate_free ~sym_def input, eval ~sym_def:sym_def (parse_term output)))
       benchmark.examples) in

  (* Time plain enumeration *)
  let prog = Program.reset first_prog (goal_type) in
  let queue = Heap.create ~min_size:100 ~cmp:Program.compare () in
  let () = Heap.add queue prog in

  let start = Unix.gettimeofday () in
  let satisfying = (*Some prog*)
    Synthesiser.enumerate_satisfying_timeout
      ~debug:false
      queue
      ~sym_lib:sym_lib_comp
      ~free_lib:free_lib
      ~sym_def:sym_def
      ~examples:examples
      max_lines in
  let stop = Unix.gettimeofday () in
  let time_plain = stop -. start in
  let solution_plain = (match satisfying with
    | Some p -> Program.to_string p
    | None -> "Not found") in

  (* Time enumeration with blacklist *)
  let prog = Program.reset first_prog (goal_type) in
  let queue = Heap.create ~min_size:100 ~cmp:Program.compare () in
  let () = Heap.add queue prog in

  let start = Unix.gettimeofday () in
  let satisfying = Some prog
    (*Synthesiser.enumerate_with_black_list_timeout
      ~debug:false
      queue
      ~sym_lib:sym_lib_comp
      ~free_lib
      ~black_list
      ~sym_def
      ~examples
      max_lines*) in
  let stop = Unix.gettimeofday () in
  let time_blacklist = stop -. start in
  let solution_blacklist = (match satisfying with
    | Some p -> Program.to_string p
    | None -> "Not found") in

  (* Time enumeration with templates *)
  let compare (prog1, n1) (prog2, n2) = Program.compare prog1 prog2 in
  let prog = Program.reset first_prog (goal_type) in
  let queue = Heap.create ~min_size:100 ~cmp:compare () in
  let () = Heap.add queue (prog,0) in

  let start = Unix.gettimeofday () in
  let satisfying = Some prog
    (*Synthesiser.enumerate_with_templates
      ~debug:false
      queue
      ~higher_order_lib:(snd (compute_sym_lib_comp ho_components))
      ~first_order_lib:(snd (compute_sym_lib_comp fo_components))
      ~free_lib
      ~sym_def
      ~black_list
      ~examples
      ~nof_hoc:2
      ~nof_hol:5
      ~nof_cal:10*) in
  let stop = Unix.gettimeofday () in
  let time_templates = stop -. start in
  let solution_templates = (match satisfying with
    | Some p -> Program.to_string p
    | None -> "Not found") in

  print_endline (sprintf
    "%s, %f, \"%s\", %f, \"%s\", %f, \"%s\", %d"
    benchmark.name
    time_plain
    solution_plain
    time_blacklist
    solution_blacklist
    time_templates
    solution_templates
    nof_components)

let test_all =

  let () = print_endline "name, time plain (s), solution plain, time with blacklist (s), solution with blacklist, time with templates (s), solution with templates, nof components" in

  List.map ~f:(test ~sym_lib_uni ~first_prog ~sym_def)  benchmarks
