(** Polymorphic λ-calculus *)

type idx_sym = string
(** Type to index symbols *)

type idx_hol = int
(** Type to index holes *)

type idx_free = int
(** Type to index input variables *)


module Kind : sig
  (** Kinds of polymorphic types *)

  type t = int
  (** Designates the number of arguments to a type *)

end

module Type : sig
  (** Polymorphic types *)

  (** Type *)
  type t =
    | Var of int
    (** De-Bruijn variable *)

    | Arr of t * t
    (** Arrow type *)

    | All of t
    (** Parametric type *)

    | Sym of idx_sym * t list
    (** Symbolic reference to a type *)

    | Hol of idx_hol
    (** Hole to be filled with a type subterm *)

    | Free of idx_free
    (** Input type variable *)

    | Int
    (** Built-in integers *)

  val to_string : t -> string
  (** Pretty-print a type *)

  val equal : t -> t -> bool
  (** Compare two types for equality *)

  val subst : t -> int -> t -> t
  (** Subtitute type subtree for a variable in a type *)

  val subst_var_in_hol : int -> idx_hol -> t -> t
  (** Substitute given variable for a hole in a type *)

  type substitution = (idx_hol, t) Hashtbl.t
  (** Type of type substitutions *)

  val subst_to_string : substitution -> string
  (** Pretty-print a substitution *)

  val apply_subst : substitution -> t -> t
  (** Apply a substitution to a type *)

end

type constraint_set = (Type.t * Type.t) list
(** Type of constraint lists *)

val unify : constraint_set -> Type.substitution
(** Unify a set of constraints *)

module Term : sig
  (** λ-terms *)

  (** Annotated λ-term

      Type and term variables use independent de Bruijn indices. *)
  type 'a t =
    | Var of 'a * int
    (** De-Bruijn variable *)

    | App of 'a * 'a t * 'a t
    (** Term application *)

    | Abs of 'a * Type.t * 'a t
    (** Term abstraction *)

    | APP of 'a * 'a t * Type.t
    (** Type application *)

    | ABS of 'a * 'a t
    (** Type abstraction *)

    | Sym of 'a * idx_sym
    (** Symbolic reference to a term *)

    | Hol of 'a * idx_hol
    (** Hole to be filled with a subterm *)

    | Free of 'a * idx_free
    (** Input variable *)

    | Int of 'a * int
    (** Built-in integer *)

    | Fun of 'a * 'a t * 'a env * 'a t option
    (** Term-argument function. The optional term is used for printing *)

    | FUN of 'a * 'a t * 'a env * 'a t option
    (** Type-argument function. The optional term is used for printing *)

    | BuiltinFun of 'a * ('a t -> 'a t) * 'a t option
    (** Built-in funtion. The optional term is used for printing *)

  and 'a env = {
    type_stack: Type.t list;
    (** Type variable bindings *)

    term_stack: 'a t list;
    (** Term variable bindings *)
  }
  (** Evaluation environment *)

  val to_string : ?debug:bool -> 'a t -> string
  (** Pretty-print a term ignoring its annotations *)

  val extract_label : 'a t -> 'a
  (** Extract annotation of a term *)

  val map_label : ('a -> 'b) -> ('b -> 'a) -> 'a t -> 'b t
  (** Apply a function to all labels of a term. The second function is something like the inverse of the first *)

  val apply_subst : Type.substitution -> 'a t -> 'a t
  (** Apply a type substitution to a term (concerns APP and ABS) *)
end


type ('i, 'm, 't) lib = {
  type_info : 'i -> 't option; (* TODO come up with better names for these fields *)
  term_info : 'i -> 'm option;
}
(** Library of term and type information *)

val empty_lib : ('i, 'm, 't) lib
(** Empty library *)
  
val expand :
  idx_sym ->
  Type.t list ->
  ?sym_def:(idx_sym, 'a Term.t, Type.t) lib ->
  ?sym_sig:(idx_sym, Type.t, Kind.t) lib ->
  Type.t
(** Expand a symbol type with its definition *)

val type_equal :
  Type.t ->
  Type.t ->
  ?sym_def:(idx_sym, 'a Term.t, Type.t) lib ->
  ?sym_sig:(idx_sym, Type.t, Kind.t) lib ->
  bool
(** Equality for types taking into account library information *)

val eval :
  ?debug:bool ->
  ?sym_def:(idx_sym, 'a Term.t, Type.t) lib ->
  ?hol_def:(idx_hol, 'a Term.t, Type.t) lib ->
  ?free_def:(idx_free, 'a Term.t, Type.t) lib ->
  'a Term.t ->
  'a Term.t
(** Evaluate a term ignoring its annotations

    In general, all functions definitions should be evaluated to Fun or FUN
    terms (i.e., no abstractions). *)


val well :
  ?sym_def:(idx_sym, 'a Term.t, Type.t) lib ->
  ?sym_sig:(idx_sym, Type.t, Kind.t) lib ->
  ?hol_sig:(idx_hol, Type.t, Kind.t) lib ->
  ?free_sig:(idx_free, Type.t, Kind.t) lib ->
  'a Term.t ->
  (Type.t option) Term.t
(** Type-check and type-annotate a term.  *)

val name : string -> 'a Term.t -> 'a Term.t
(** Set a function name if not set *)

(* TODO implement a nice API for definig libraries (see test_lambda.ml for the low-level hell) *)

(* TODO currently documentation is scattered around.  Consolidate and improve *)
