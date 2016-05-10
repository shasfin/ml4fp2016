module Library : sig

  type 'i t = {
    (* TODO Maybe we should hide the actual type *)
    (* TODO Maybe we want to make it polymorphic *)
    termtbl : ('i, (Type.t Term.t, Type.t)) Hashtbl.t;
    typetbl : ('i, (Type.t, Kind.t)) Hashtbl.t;
  }

  val add_term : idx -> Type.t Term.t -> Type.t -> -> Library.t -> unit
  (** Add a term component to the library *)

  val add_type : (idx -> Type.t -> Kind.t) -> Library.t -> unit
  (** Add a type component to the library *)

  val get_lib_def : Library.t -> (idx, Term.t, Type.t) lib
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
