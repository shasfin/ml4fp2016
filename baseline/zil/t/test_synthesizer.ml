open TestSimple;;
open Printf;;

open Zil.Lambda;;
open Zil.Parse;;
open Zil;;

(******************************************************************************)
(* Define library *)

let sym_lib = Library.create ();;

(* We do not need to type the definitions of the library functions.
 * We can just put unit Term.t in it. They are used only for evaluation and evaluation does not use the annotations.
 * For evaluation we can do a map_label (fun _ -> unit), so it will typecheck *)

(* Types *)
(* Recursive lists *)
let list_sig = 1
let list_def = parse_type "@ #0 -> (#1 -> List #1 -> #0) -> #0";;

let () = Library.add_type "List" list_def list_sig sym_lib;;

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

(* functions *)
let list_map_sig = parse_type "@ @ (#1 -> #0) -> List #1 -> List #0";;
let list_map_def = parse_term "* * { [#1 -> #0] [List #1] : $0 #0 (nil #0) { [#1] [List #1] : con #0 ($3 $1) (map #1 #0 $3 $0) } }";;
let list_map_fun = name "map" (eval list_map_def);;

let () = Library.add_term "map" list_map_fun list_map_sig sym_lib;;



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
let test_enumeration ?msg:(msg="Basic enumeration") goal_type free_lib =
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

  let nof_programs = 4 in

  let queue = Queue.create () in
  let () = Queue.add prog queue in

(* TODO debugging *) let () = print_string "Printing free_lib...\n" in
   let () = print_free_lib free_lib in
   let () = print_string "________________\n" in
   let () = print_string "Printing sym_lib_uni...\n" in
   let () = print_sym_lib sym_lib_uni in
   let () = print_string "________________\n\n" in (* end *)

  Synthesiser.enumerate queue sym_lib_uni free_lib nof_programs



(* easy test: try to generate map itself *)
let free_lib = Library.create ();;
let map_test = test_enumeration ~msg:"Try to generate map" list_map_sig free_lib;;
let () =  print_string (String.concat "\n" (List.map Program.to_string map_test));;

