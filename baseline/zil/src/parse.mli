(** Short-hand interface to the parser *)

open Lambda

val parse_type : string -> Lambda.Type.t
(** Parse a type in a string *)

val parse_term : string -> unit Lambda.Term.t
(** Parse a term in a string *)
