(** Basic program enumerator *)
open Lambda


module IntMap : sig
  type 'a t
end

module Program : sig
  (** Type of generated partial programs *)

  type t = {
    max_term_hol : idx_hol; (* first fresh term hole index *)
    max_type_hol : idx_hol; (* first fresh type hole index *)
    current_term_hol : idx_hol; (* smallest expandable term hole *)
    prog : (Type.t Term.t option * Type.t) IntMap.t;
    (** A program is a mapping from holes to the corresponding terms, if present, and to their types. The starting point is ?0 *)
  }

  val create : unit -> t

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

  val apply_subst : substitution -> t -> t
  (** Apply substitution to all types of the program *)

end

val successor :
  Program.t ->
  sym_lib:(idx_sym, Type.t) Library.t ->
  free_lib:(idx_free, Type.t) Library.t ->
  Program.t list
(** Expand current term hole of a program *)

val enumerate :
  Program.t Queue.t ->
  sym_lib:(idx_sym, Type.t) Library.t ->
  free_lib:(idx_free, Type.t) Library.t ->
  int ->
  Program.t list
(** Enumerate first closed programs found by BFS from the queue *)
  
