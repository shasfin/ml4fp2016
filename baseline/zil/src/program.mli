(** Partial programs with holes *)
open Lambda


module IntMap : sig
  type 'a t
end

module StringMap : sig
  type 'a t
end

  (** Type of generated partial programs *)

  type t = {
    max_term_hol : idx_hol; (* first fresh term hole index *)
    max_type_hol : idx_hol; (* first fresh type hole index *)
    open_holes : idx_hol list; (* stack of open holes *)
    closed_holes : idx_hol list; (* stack of closed holes *)
    components : int StringMap.t; (* association list of used components *)
    prog : (Type.t Term.t option * Type.t) IntMap.t;
    (** A program is a mapping from holes to the corresponding terms, if present, and to their types. The starting point is ?0 *)
  }

  val create : unit -> t

  val reset : t -> Type.t -> t

  val is_closed : t -> bool
  (** True if there are no holes to expand *)

  val current_type : t -> Type.t
  (** The type of the next hole to expand *)

  val get_fresh_term_hol : Type.t -> t -> Type.t Term.t * t
  (** Returns a fresh term hole with the given type and the updated program *)

  val get_fresh_type_hol : t -> Type.t * t
  (** Returns a fresh type hole and the updated program *)

  val expand_current_hol : Type.t Term.t -> t -> t
  (** Expand current hole with a term *)

  val close_current_hol : t -> t
  (** Make current hole non-expandable *)

  val open_all_closed_holes : t -> t
  (** Transform all non-expandable holes into expandable holes *)

  val nof_holes : t -> int
  (** Number of holes *)

  val apply_subst : Type.substitution -> t -> t
  (** Apply substitution to all types of the program *)

  val to_term : t -> Type.t Term.t
  (** Convert a program to a typed term *)
  
  val to_string : t -> string
  (** Print a program as a term *)

  val to_string_typed : t -> string
  (** Print a program as a table of hole to type bindings *)
  
  val eval :
    ?sym_def:(idx_sym, unit Term.t, Type.t) lib ->
    ?hol_def:(idx_hol, unit Term.t, Type.t) lib ->
    ?free_def:(idx_free, unit Term.t, Type.t) lib ->
    t ->
    unit Term.t
  (** Evaluate the program to a term *)

  val compare : t -> t -> int
  (** Comparison function based on the number of open holes *)
	
