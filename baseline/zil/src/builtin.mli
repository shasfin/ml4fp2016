open Lambda

val zero : idx_sym * unit Term.t * Type.t
val succ : idx_sym * unit Term.t * Type.t

val add : idx_sym * unit Term.t * Type.t
val sub : idx_sym * unit Term.t * Type.t
val mul : idx_sym * unit Term.t * Type.t
val div : idx_sym * unit Term.t * Type.t
val max : idx_sym * unit Term.t * Type.t
val foldNat : idx_sym * unit Term.t * Type.t
val foldNatNat : idx_sym * unit Term.t * Type.t
val is_zero : idx_sym * unit Term.t * Type.t
