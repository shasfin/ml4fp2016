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

  val is_closed : t -> bool

  val current_type : t -> Type.t

end

val successor :
  Program.t ->
  sym_sig:(idx_sym, Type.t) Hashtbl.t ->
  free_sig:(idx_free, Type.t) Hashtbl.t ->
  Program.t list
(** Expand current term hole of a program *)

val enumerate :
  Program.t Queue.t ->
  sym_sig:(idx_sym, Type.t) Hashtbl.t ->
  free_sig:(idx_free, Type.t) Hashtbl.t ->
  int ->
  Program.t list
(** Enumerate first closed programs found by BFS from the queue *)
  
