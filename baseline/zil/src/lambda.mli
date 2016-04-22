(** Polymorphic λ-calculus *)

type idx_sym = string
(** Type to index symbols *)

type idx_hol = int
(** Type to index holes *)


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

  val to_string : t -> string
  (** Pretty-print a type *)

end

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

    | Fun of 'a * 'a t * 'a env * 'a t option
    (** Term-argument function. The optional term is used for printing *)

    | FUN of 'a * 'a t * 'a env * 'a t option
    (** Type-argument function. The optional term is used for printing *)

  and 'a env = {
    type_stack: Type.t list;
    (** Type variable bindings *)

    term_stack: 'a t list;
    (** Term variable bindings *)
  }
  (** Evaluation environment *)

  val to_string : 'a t -> string
  (** Pretty-print a term ignoring its annotations *)

end


type ('i, 'm, 't) lib = {
  type_info : 'i -> 't option; (* TODO come up with better names for these fields *)
  term_info : 'i -> 'm option;
}
(** Library of term and type information *)

  
val eval :
  ?sym_def:(idx_sym, 'a Term.t, Type.t) lib ->
  ?hol_def:(idx_hol, 'a Term.t, Type.t) lib ->
  'a Term.t ->
  'a Term.t
(** Evaluate a term ignoring its annotations

    In general, all functions definitions should be evaluated to Fun or FUN
    terms (i.e., no abstractions). *)


val well :
  ?sym_sig:(idx_sym, Type.t, Kind.t) lib ->
  ?hol_sig:(idx_hol, Type.t, Kind.t) lib ->
  'a Term.t ->
  (Type.t option) Term.t
(** Type-check and type-annotate a term.  *)

val name : string -> 'a Term.t -> 'a Term.t
(** Set a function name if not set *)

(* TODO implement a nice API for definig libraries (see test_lambda.ml for the low-level hell) *)

(* TODO currently documentation is scattered around.  Consolidate and improve *)
