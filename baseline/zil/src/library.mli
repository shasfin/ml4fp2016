open Lambda

type ('i, 'a) t
(** 'i is the type of the index of the component, 'a is the type of the annotation of the terms that define the components *)

val add_term : 'i -> 'a Term.t -> Type.t -> ('i, 'a) t -> unit
(** Add a term component to the library *)

val add_type : 'i -> Type.t -> Kind.t -> ('i, 'a) t -> unit
(** Add a type component to the library *)

val get_lib_def : ('i, 'a) t -> ('i, 'a Term.t, Type.t) lib
(** Convert library to the lib type defined in Lambda and used for evaluation *)

val get_lib_sig: ('i, 'a) t -> ('i, Type.t, Kind.t) lib
(** Convert library to the lib type defined in Lambda and used for evaluation *)

val lookup_term_def : ('i, 'a) t -> 'i -> 'a Term.t
(** Lookup the definition of a term library component. Raises Not Found exception *)

val lookup_term_sig : ('i, 'a) t -> 'i -> Type.t
(** Lookup the signature of a term library component. Raises Not Found exception *)

val lookup_type_def : ('i, 'a) t -> 'i -> Type.t
(** Lookup the definition of a type library component. Raises Not Found exception *)

val lookup_type_sig : ('i, 'a) t -> 'i -> Kind.t
(** Lookup the signature of a type library component. Raises Not Found exception *)

val unifiable_term_sigs : ('i, 'a) t -> Type.t -> ('i * Type.t * substitution) list
