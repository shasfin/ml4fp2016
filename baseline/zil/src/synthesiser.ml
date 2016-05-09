open Printf
open Lambda
open Parse

(******************************************************************************)
module IntMap = Map.Make(struct type t = int let compare = compare end)

module Program = struct

    type t = {
        max_term_hol: idx_hol; (* first fresh hole index *)
        max_type_hol: idx_hol; (* firse fresh type hole index *)
        current_term_hol: idx_hol; (* smallest expandable hole *)
        prog: (Type.t Term.t option * Type.t) IntMap.t; (* mapping from term holes to terms and types *)
    }

    let is_closed ctxt = ctxt.current_term_hol >= ctxt.max_term_hol
    (* if the hole to expand is a fresh hole, then the program is closed *)

    (* TODO think which functions should be defined in this module,
     * for example eval or first program given a goal type or something like that *)
end
        
(******************************************************************************)

open Program
(* Expand only one of the holes, the open hole with the smallest number. Returns a list of contexts *)
(* ctxt is of type Program.t *)
(* sym_sig and free_sig are hashtbls *)
let successor ctxt sym_sig free_sig =
    let succ_app =
        let current_type = snd (IntMap.find ctxt.current_term_hol ctxt.prog) in
        let a = (Type.Arr (Type.Hol ctxt.max_type_hol, current_type)) in
        let b = Type.Hol ctxt.max_type_hol in
        let current_term =
            Term.App (current_type,
                      Term.Hol (a, ctxt.max_term_hol),
                      Term.Hol (b, ctxt.max_term_hol+1)) in
        let new_prog = IntMap.add ctxt.current_term_hol (Some current_term, current_type) ctxt.prog in
        let new_prog = IntMap.add ctxt.max_term_hol (None, a) new_prog in
        let new_prog = IntMap.add ctxt.max_term_hol (None, b) new_prog

        in [{max_term_hol = ctxt.max_term_hol + 2;
             max_type_hol = ctxt.max_type_hol + 1;
             current_term_hol = ctxt.current_term_hol + 1;
             prog = new_prog}]

    let succ_free =

        (* TODO implement succ_free (lookup and unification in free_sig) *)

    (* TODO implement succ_sym (lookup and unification if sym_sig *)

    in
      if Program.is_closed ctxt
      then []
      else succ_app @ succ_free @ succ_sym

(* Evaluate such an association list *)
 

(******************************************************************************)


(******************************************************************************)
