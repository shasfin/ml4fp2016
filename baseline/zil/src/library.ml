open Lambda

type ('i, 'a) t = {
  termtbl : ('i, 'a Term.t * Type.t) Hashtbl.t;
  typetbl : ('i,  Type.t * Kind.t) Hashtbl.t;
}

let add_term i m a lib = Hashtbl.replace lib.termtbl i (m, a)

let add_type i a k lib = Hashtbl.replace lib.typetbl i (a, k)

let get_map_fun f tbl =
    (fun x -> if Hashtbl.mem tbl x then Some (f (Hashtbl.find tbl x)) else None)

let get_lib_def lib = {
    term_info = get_map_fun fst lib.termtbl;
    type_info = get_map_fun fst lib.typetbl;
}

let get_lib_sig lib = {
  term_info = get_map_fun snd lib.termtbl;
  type_info = get_map_fun snd lib.typetbl;
}

let lookup_term_def lib i = fst (Hashtbl.find lib.termtbl i)

let lookup_term_sig lib i = snd (Hashtbl.find lib.termtbl i)

let lookup_type_def lib i = fst (Hashtbl.find lib.typetbl i)

let lookup_type_sig lib i = snd (Hashtbl.find lib.typetbl i)

let unifiable_term_sigs lib a =
  Hashtbl.fold
    (fun key (_, value) l ->
      try (key, value, unify [(a, value)]) :: l
      with Invalid_argument _ -> l)
    lib.termtbl
    [] 

    
