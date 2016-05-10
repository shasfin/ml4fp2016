open Lambda

module Library = struct
    type 'i t = {
    (* TODO Maybe we should hide the actual type *)
    (* TODO Maybe we want to make it polymorphic *)
    termtbl : 'i  (Type.t Term.t * Type.t) Hashtbl.t;
    typetbl : 'i  (Type.t * Kind.t) Hashtbl.t;
  }

  let add_term i m a lib = Hashtbl.replace lib.termtbl i (m, a)

  let add_type i a k lib = Hashtbl.replace lib.typetbl i (a, k)

  let get_fun

  let get_lib_def lib = {
      term_info = get_fun termtbl;
  type_info = get_fun typetbl;
    }
      : Library.t -> (idx, Term.t, Type.t) lib
  (** Convert library to the lib type defined in Lambda and used for evaluation *)

  val get_lib_sig: Library.t -> (idx, Type.t, Kind.t) lib
  (** Convert library to the lib type defined in Lambda and used for evaluation *)

  val lookup_term_def : Library.t -> idx -> Term.t
  (** Lookup the definition of a term library component *)

  val lookup_term_sig : Library.t -> idx -> Type.t
  (** Lookup the signature of a term library component *)

  val lookup_type_def : Library.t -> idx -> Type.t
  (** Lookup the definition of a type library component *)

  val lookup_type_sig : Library.t -> idx -> Kind.t
  (** Lookup the signature of a type library component *)


end
      
