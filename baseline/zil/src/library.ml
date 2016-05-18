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

let lookup_term_def lib i = (fun (x, _, _) -> x) (Hashtbl.find lib.termtbl i)

let lookup_term_sig lib i = (fun (_, x, _) -> x) (Hashtbl.find lib.termtbl i)

let lookup_type_def lib i = fst (Hashtbl.find lib.typetbl i)

let lookup_type_sig lib i = snd (Hashtbl.find lib.typetbl i)

let unifiable_term_sigs lib a =
  Hashtbl.fold
    (fun key (_, value, args) l ->
      try (key, value, unify [(a, value)], args) :: l
      with Invalid_argument _ -> l)
    lib.termtbl
    [] 

let fold_terms f lib init = Hashtbl.fold (fun i (m, a, args) -> f i m a args) lib.termtbl init

let fold_types g lib init = Hashtbl.fold (fun i (a, k) -> g i a k) lib.typetbl init

let fold f g lib init = fold_types g lib (fold_terms f lib init)

let iter_terms f lib = Hashtbl.iter (fun i (m, a, args) -> f i m a args) lib.termtbl

let iter_types g lib = Hashtbl.iter (fun i (a, k) -> g i a k) lib.typetbl

let iter f g lib = iter_terms f lib ; iter_types g lib
