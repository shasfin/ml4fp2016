open Printf
open Lambda
open Parse

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
type program = (idx_hol, Type.t Term.t option * Type.t) Hashtbl.t
(* A program is a mapping from a hole number to its type and maybe to the annotated term that was substituted into that hole. The starting point is the hole ?0 *)
type context = idx_hol * idx_hol * idx_hol * program
(* max_term_hol is the first fresh term hole index still unused in the program
 * max_type_hol is the first fresh type hole index still unused in the program
 * current_term_hol is the smallest term hole index of an "open" hole in the program*)

(* Expand only one of the holes, the open hole with the smallest number. Returns a list of contexts *)
let successor ctxt sym_sig free_sig =
    let succ_app = match ctxt with
    | (max_term_hol, max_type_hol, current_term_hol, prog) ->
        let current_type = snd (Hashtbl.find prog current_term_hol) in
        let a = (Type.Arr (Type.Hol max_type_hol, current_type)) in
        let b = Type.Hol max_type_hol in
        let current_term =
            Term.App (current_type,
                      Term.Hol (a, max_term_hol),
                      Term.Hol (b, max_term_hol+1)) in
        let new_prog = Hashtbl.copy prog in 
        let () = Hashtbl.replace new_prog current_term_hol (Some current_term, current_type) in
        let () = Hashtbl.replace new_prog max_term_hol (None, a) in
        let () = Hashtbl.replace new_prog max_term_hol (None, b)

        in [(max_term_hol + 2,
             max_type_hol + 1,
             current_term_hol + 1,
             new_prog)]

    let succ_free = match ctxt with
    | (max_term_hol, max_type_hol, current_term_hol, prog) ->
        (* TODO implement succ_free (lookup and unification in free_sig) *)

    (* TODO implement succ_sym (lookup and unification if sym_sig *)

    in succ_app @ succ_free @ succ_sym

(* Evaluate such an association list *)
 

(******************************************************************************)


(******************************************************************************)
