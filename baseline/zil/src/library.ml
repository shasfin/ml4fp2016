open Lambda
open Printf

type ('i, 'a) t = {
  (* The list is needed only for sym_libs that are prepared for unification.
   * It contains the type application arguments (holes) that were applied in order to get rid of the universal types and enable unification *)
  termtbl : ('i, 'a Term.t * Type.t * (Type.t list)) Hashtbl.t;
  typetbl : ('i,  Type.t * Kind.t) Hashtbl.t;
}

let initial_guess = 10

let create () = {
    termtbl = Hashtbl.create initial_guess;
    typetbl = Hashtbl.create initial_guess;
}

let add_term i m a ?typ_args:(typ_args=[]) lib = Hashtbl.replace lib.termtbl i (m, a, typ_args)

let add_type i a k lib = Hashtbl.replace lib.typetbl i (a, k)

let get_map_fun f tbl =
    (fun x -> if Hashtbl.mem tbl x then Some (f (Hashtbl.find tbl x)) else None)

let get_lib_def lib = {
    term_info = get_map_fun (fun (x, _, _) -> x) lib.termtbl;
    type_info = get_map_fun fst lib.typetbl;
}

let get_lib_sig lib = {
  term_info = get_map_fun (fun (_, x, _) -> x) lib.termtbl;
  type_info = get_map_fun snd lib.typetbl;
}

let lookup_term lib i = Hashtbl.find lib.termtbl i

let lookup_type lib i = Hashtbl.find lib.typetbl i

let lookup_term_def lib i = (fun (x, _, _) -> x) (Hashtbl.find lib.termtbl i)

let lookup_term_sig lib i = (fun (_, x, _) -> x) (Hashtbl.find lib.termtbl i)

let lookup_type_def lib i = fst (Hashtbl.find lib.typetbl i)

let lookup_type_sig lib i = snd (Hashtbl.find lib.typetbl i)

let unifiable_term_sigs lib a =
  Hashtbl.fold
    (fun key (_, value, args) l ->
      try (key, value, unify [(a, value)], args) :: l
      (*(* TODO debugging *) with Invalid_argument str -> print_string ("   " ^str ^ "\n") ; l)*) with Invalid_argument _ -> l)
    lib.termtbl
    [] 

let fold_terms f lib init = Hashtbl.fold (fun i (m, a, args) -> f i m a args) lib.termtbl init

let fold_types g lib init = Hashtbl.fold (fun i (a, k) -> g i a k) lib.typetbl init

let fold f g lib init = fold_types g lib (fold_terms f lib init)

let iter_terms f lib = Hashtbl.iter (fun i (m, a, args) -> f i m a args) lib.termtbl

let iter_types g lib = Hashtbl.iter (fun i (a, k) -> g i a k) lib.typetbl

let iter f g lib = iter_terms f lib ; iter_types g lib

let to_string f g lib =
  String.concat "\n"
    (fold
      (fun i m a args acc ->
        (sprintf
          "%s | %s | %s"
          (Term.to_string (f i))
          (Term.to_string m)
          (Type.to_string a))::acc
      )
      (fun i a k acc ->
        (sprintf
          "%s | %s | %s"
          (Type.to_string (g i))
          (Type.to_string a)
          (string_of_int k))::acc
      )
      lib
      []
    )


let read_from_file filename =
 
  let well_typed i m a sym_def sym_sig =
    let m = match m with
    | Term.Fun (_, def, env, alt) -> def
    | Term.FUN (_, def, env, alt) -> def
    | m -> m in
    let annotated =
        (try well ~sym_def:sym_def ~sym_sig:sym_sig m
         with Invalid_argument s -> invalid_arg (sprintf "Problem by typechecking %s. %s" i s)) in
    let got_type = match (Term.extract_label annotated) with
      | Some b -> b
      | None -> invalid_arg (sprintf "Could not typecheck %s" i) in
    if (type_equal got_type a ~sym_def:sym_def ~sym_sig:sym_sig)
    then true
    else invalid_arg (sprintf
      "Problem by typechecking %s. Reconstructed type %s does not agree with expected type %s"
      i
      (Type.to_string got_type)
      (Type.to_string a)) in

  let lib = create () in
  let term_regexp = Str.regexp "^\\([a-z].*\\) | \\(.*\\) | \\(.*\\)$" in
  let type_regexp = Str.regexp "^\\([A-Z].*\\) | \\(.*\\) | \\(.*\\)$" in
  let comment_regexp = Str.regexp "^--.*$" in
  let error_regexp = Str.regexp "^[^-A-Za-z].*$" in
  let sep = Str.regexp_string " | " in

  let read_lines name : string list =
    let ic = open_in name in
    let try_read () =
      try Some (input_line ic) with End_of_file -> None in
    let rec loop acc = match try_read () with
      | Some s -> if (String.trim s = "")
                  then loop acc (* ignore empty lines *)
                  else loop (s::acc)
      | None -> close_in ic; acc in
    loop [] in

  let parse_and_add line =
    if Str.string_match term_regexp line 0
    then let [i; m; a] = Str.split sep line in
      add_term i (Parse.parse_term m) (Parse.parse_type a) lib
    else if Str.string_match type_regexp line 0
    then let [i; a; k] = Str.split sep line in
      add_type i (Parse.parse_type a) (int_of_string k) lib
    else if Str.string_match comment_regexp line 0
    then ()
    else if Str.string_match error_regexp line 0
    then invalid_arg (sprintf "Syntax error. \"%s\" is an invalid line" line)
    else invalid_arg (sprintf "Unknown error on line \"%s\"" line) in

  let lines = read_lines filename in
  let () = List.iter parse_and_add lines in
  (*let () = print_string (to_string (fun x -> Term.Sym ((), x)) (fun x -> Type.Sym (x,[])) lib) in*)
  let sym_def = get_lib_def lib in
  let sym_sig = get_lib_sig lib in
  let () = Hashtbl.filter_map_inplace
    (fun i (m, a, args) -> if (well_typed i m a sym_def sym_sig) then Some (name i (eval m), a, args) else None)
    lib.termtbl in
  lib

