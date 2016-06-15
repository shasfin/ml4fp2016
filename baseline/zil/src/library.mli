open Lambda

type ('i, 'a) t
(** 'i is the type of the index of the component, 'a is the type of the annotation of the terms that define the components *)

val create : unit -> ('i, 'a) t
(** Create an empty library *)

val add_term : 'i -> 'a Term.t -> Type.t -> ?typ_args : Type.t list -> ('i, 'a) t -> unit
(** Add a term component to the library *)

val add_type : 'i -> Type.t -> Kind.t -> ('i, 'a) t -> unit
(** Add a type component to the library *)

val get_lib_def : ('i, 'a) t -> ('i, 'a Term.t, Type.t) lib
(** Convert library to the lib type defined in Lambda and used for evaluation *)

val get_lib_sig: ('i, 'a) t -> ('i, Type.t, Kind.t) lib
(** Convert library to the lib type defined in Lambda and used for evaluation *)

val read_from_file : string -> (idx_sym, unit) t
(** Read a sym lib from file *)

val lookup_term : ('i, 'a) t -> 'i -> ('a Term.t * Type.t * Type.t list)
(** Get the whole term record *)

val lookup_type : ('i, 'a) t -> 'i -> (Type.t * Kind.t)
(** Get the whole type record *)

val lookup_term_def : ('i, 'a) t -> 'i -> 'a Term.t
(** Lookup the definition of a term library component. Raises Not Found exception *)

val lookup_term_sig : ('i, 'a) t -> 'i -> Type.t
(** Lookup the signature of a term library component. Raises Not Found exception *)

val lookup_type_def : ('i, 'a) t -> 'i -> Type.t
(** Lookup the definition of a type library component. Raises Not Found exception *)

val lookup_type_sig : ('i, 'a) t -> 'i -> Kind.t
(** Lookup the signature of a type library component. Raises Not Found exception *)

val unifiable_term_sigs : ('i, 'a) t -> Type.t -> ('i * Type.t * Type.substitution * (Type.t list)) list
(** Returns the list of components that unify with the given type *)

val fold_terms : ('i -> 'a Term.t -> Type.t -> Type.t list -> 'c -> 'c) -> ('i, 'a) t -> 'c -> 'c
(** Fold term definitions and signatures *)

val fold_types : ('i -> Type.t -> Kind.t -> 'c -> 'c) -> ('i, 'a) t -> 'c -> 'c
(** Fold type definitions and signatures *)

val fold :
  ('i -> 'a Term.t -> Type.t -> Type.t list -> 'c -> 'c) ->
  ('i -> Type.t -> Kind.t -> 'c -> 'c) ->
  ('i, 'a) t ->
  'c ->
  'c
(** Fold over terms and types: fold f g lib init folds the terms using the function f and the initial value init and then folds the types using the function g and the result of the fold of the terms as initial value *)

val iter_terms :
  ('i -> 'a Term.t -> Type.t -> Type.t list -> unit) ->
  ('i, 'a) t ->
  unit
(** Iterate over term definitions and signatures *)

val iter_types :
  ('i -> Type.t -> Kind.t -> unit) ->
  ('i, 'a) t ->
  unit
(** Iterate over type definitions and signatures *)

val iter :
  ('i -> 'a Term.t -> Type.t -> Type.t list -> unit) ->
  ('i -> Type.t -> Kind.t -> unit) ->
  ('i, 'a) t ->
  unit
(** Iterate the first function over terms and the second over types *)

val to_string :
  ('i -> 'a Term.t) ->
  ('i -> Type.t) ->
  ('i, 'a) t ->
  string
(** Pretty print a library *)

