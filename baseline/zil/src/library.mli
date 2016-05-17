open Lambda

type ('i, 'a) t
(** 'i is the type of the index of the component, 'a is the type of the annotation of the terms that define the components *)

val create : unit -> ('i, 'a) t

val add_term : 'i -> 'a Term.t -> Type.t -> ?typ_args : Type.t list -> ('i, 'a) t -> unit
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

val unifiable_term_sigs : ('i, 'a) t -> Type.t -> ('i * Type.t * substitution * (Type.t list)) list
(** Returns the list of components that unify with the given type *)

val fold_terms : ('i -> 'a Term.t -> Type.t -> Type.t list -> 'c -> 'c) -> ('i, 'a) t -> 'c -> 'c
(** Fold term definitions and signatures *)

val fold_types : ('i -> Type.t -> Kind.t -> 'c -> 'c) -> ('i, 'a) t -> 'c -> 'c
(** Fold type definitions and signatures *)
