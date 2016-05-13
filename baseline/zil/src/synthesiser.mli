(** Basic program enumerator *)
open Lambda

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
  
