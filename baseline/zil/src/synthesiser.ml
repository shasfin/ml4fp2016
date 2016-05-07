open Printf

(******************************************************************************)
(* I need a queue of partial programs *)
(* A partial program is represented by a max hole (first unused hole index) and a list of hole to term bindings *)
(* Not to forget, I also need the library with the inputs and the components (can be reused) and a list of hole to type bindings (each partial program needs the own) *)
(*
Suppose, we will start with hole ?x1 of type T. The hol-to-term will be empty, max will be 2 and hol-to-type will contain 1->T.
Then we will apply the successor function and create a list of successors, among which will be the program ?x2 ?x3. Now hol-to-term will contain 1->?x2 ?x3 and hol-to-type will contain 1->T, 2->(^1 -> T) and 3->^1 and max will be 4.
Look, we also need to know which is the next fresh hole type variable.
context = int * int, that ist (next_fresh_hole_index, next_fresh_type_hole_index)
program = (hol_idx * Term.t) list (association list)
type_info = (hol_idx * Type.t) list (association list)
Program and type_info should go hand in hand. Maybe a triple association list? idx_hol * Term.t * Type.t? But sometimes we have only the type information. Those are the holes we want to expand.
The hole-to-expand should also be part of the context. Otherwise it is not very efficient to look it up every time.
*)

type context = idx_hol * idx_hol

(* Expand only one of the holes, the open hole with the smallest number. Returns a list of (program * hol_sig)s. And the new context, of course. How can we return all those things? Just as a tuple? Well, each program has its own. *)
let successor ctxt program hol_sig

(* Evaluate such an association list *)
let 

(******************************************************************************)



(******************************************************************************)