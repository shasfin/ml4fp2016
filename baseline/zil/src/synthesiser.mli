(** Basic program enumerator *)
open Core.Std
open Lambda

val prepare_lib : ('i, 'a) Library.t -> Program.t -> (('i, 'a) Library.t * Program.t)
(** Prepare library for unification by deuniversalising all universal types *)

val successor :
  Program.t ->
  sym_lib:(idx_sym, Type.t) Library.t ->
  free_lib:(idx_free, Type.t) Library.t ->
  Program.t list
(** Expand current term hole of a program *)

val enumerate :
  Program.t Heap.t ->
  sym_lib:(idx_sym, 'a) Library.t ->
  free_lib:(idx_free, 'a) Library.t ->
  int ->
  Program.t list
(** Enumerate first closed programs found by BFS from the queue *)

val filter_satisfying :
  Program.t list ->
  ((idx_free, unit Term.t, Type.t) lib * unit Term.t) list ->
  ?sym_def:(idx_sym, unit Term.t, Type.t) lib ->
  Program.t list
(** Given a list of programs, return the list of programs that satisfy all the I/O-examples *)

val enumerate_satisfying :
  Program.t Heap.t ->
  sym_lib:(idx_sym, unit) Library.t ->
  free_lib:(idx_free, unit) Library.t ->
  ?examples:((idx_free, unit Term.t, Type.t) lib * unit Term.t) list ->
  int ->
  Program.t list
(** Enumerate first satisfying programs found by BFS from the queue *)
