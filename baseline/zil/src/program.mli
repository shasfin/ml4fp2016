(** Partial programs with holes *)
open Lambda


module IntMap : sig
  type 'a t
end

  (** Type of generated partial programs *)

  type t = {
    max_term_hol : idx_hol; (* first fresh term hole index *)
    max_type_hol : idx_hol; (* first fresh type hole index *)
    current_term_hol : idx_hol; (* smallest expandable term hole *)
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

  val apply_subst : Type.substitution -> t -> t
  (** Apply substitution to all types of the program *)

  val to_term : t -> Type.t Term.t
  (** Convert a program to a typed term *)
  
  val to_string : t -> string
  (** Print a program as a term *)

  val to_string_typed : t -> string
  (** Print a program as a table of hole to type bindings *)
  
  val eval :
    ~sym_lib:(idx_sym, 'a) Library.t ->
	~hol_lib:(idx_hol, 'a) Library.t ->
	~free_lib:(idx_free, 'a) Library.t ->
	t ->
	Term.t
  (** Evaluate the program to a term *)
	
