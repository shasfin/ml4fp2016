(** Basic program enumerator *)
open Core.Std
open Lambda

val prepare_lib : ('i, 'a) Library.t -> Program.t -> (('i, 'a) Library.t * Program.t)
(** Prepare library for unification by deuniversalising all universal types *)

val successor :
  ?debug:bool ->
  Program.t ->
  sym_lib:(idx_sym, Type.t) Library.t ->
  free_lib:(idx_free, Type.t) Library.t ->
  Program.t list
(** Expand current term hole of a program *)

val enumerate :
  ?debug:bool ->
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
  ?debug:bool ->
  Program.t Heap.t ->
  sym_lib:(idx_sym, unit) Library.t ->
  free_lib:(idx_free, unit) Library.t ->
  ?sym_def:(idx_sym, unit Term.t, Type.t) lib ->
  ?examples:((idx_free, unit Term.t, Type.t) lib * unit Term.t) list ->
  int ->
  Program.t list
(** Enumerate first satisfying programs found by BFS from the queue *)

val enumerate_satisfying_timeout :
  ?debug:bool ->
  Program.t Heap.t ->
  sym_lib:(idx_sym, unit) Library.t ->
  free_lib:(idx_free, unit) Library.t ->
  ?sym_def:(idx_sym, unit Term.t, Type.t) lib ->
  ?examples:((idx_free, unit Term.t, Type.t) lib * unit Term.t) list ->
  int ->
  Program.t option
(** Try to find first satisfying program before reaching 4*max_lines successors *)


val enumerate_with_black_list :
  ?debug:bool ->
  Program.t Heap.t ->
  sym_lib:(idx_sym, unit) Library.t ->
  free_lib:(idx_free, unit) Library.t ->
  black_list:('a Term.t list) ->
  ?sym_def:(idx_sym, unit Term.t, Type.t) lib ->
  ?examples:((idx_free, unit Term.t, Type.t) lib * unit Term.t) list ->
  int ->
  Program.t list
(** Enumerate first satisfying programs found by BFS from the queue, prune according to black_list *)

val enumerate_with_black_list_timeout :
  ?debug:bool ->
  Program.t Heap.t ->
  sym_lib:(idx_sym, unit) Library.t ->
  free_lib:(idx_free, unit) Library.t ->
  black_list:('a Term.t list) ->
  ?sym_def:(idx_sym, unit Term.t, Type.t) lib ->
  ?examples:((idx_free, unit Term.t, Type.t) lib * unit Term.t) list ->
  int ->
  Program.t option
(** Try to find first satisfying program before reaching 4*max_lines successors using pruning based on a black list *)

val enumerate_with_templates :
  ?debug:bool ->
  (Program.t * int) Heap.t ->
  higher_order_lib:(idx_sym, unit) Library.t ->
  first_order_lib:(idx_sym, unit) Library.t ->
  free_lib:(idx_free, unit) Library.t ->
  black_list:('a Term.t list) ->
  sym_def:(idx_sym, unit Term.t, Type.t) lib ->
  ?examples:((idx_free, unit Term.t, Type.t) lib * unit Term.t) list ->
  nof_hoc:int ->
  nof_hol:int ->
  nof_cal:int ->
  Program.t option
(** Enumerate first satisfying program using two queues: one to find a template, the other to search a program from that template. This is the variant with the black_list *)

