(** Basic program enumerator *)

module IntMap = Map.Make(struct type t = int let compare = compare end)

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

end

val successor : Program.t -> Program.t list
