open Printf
open Lambda

module IntMap = Map.Make(struct type t = int let compare = compare end)

type t = {
    max_term_hol: idx_hol; (* first fresh hole index *)
    max_type_hol: idx_hol; (* firse fresh type hole index *)
    current_term_hol: idx_hol; (* smallest expandable hole *)
    prog: (Type.t Term.t option * Type.t) IntMap.t; (* mapping from term holes to terms and types *)
}

(* Create the empty program. Note that it is considered closed *)
let create () = {
    max_term_hol = 0;
    max_type_hol = 0;
    current_term_hol = 0;
    prog = IntMap.empty;
}

(* Generate the first program consisting of a hole of a given type from an existing program. Only the information about used type holes is preserved *)
let reset prog a = {
    max_term_hol = 1;
    max_type_hol = prog.max_type_hol;
    current_term_hol = 0;
    prog = IntMap.add 0 (None, a) IntMap.empty;
}

let is_closed ctxt = ctxt.current_term_hol >= ctxt.max_term_hol
(* if the hole to expand is a fresh hole, then the program is closed *)

let current_type ctxt = snd (IntMap.find ctxt.current_term_hol ctxt.prog)

let get_fresh_term_hol a prog =
    (Term.Hol (a, prog.max_term_hol),
    {max_term_hol = prog.max_term_hol + 1;
     max_type_hol = prog.max_type_hol;
     current_term_hol = prog.current_term_hol;
     prog = IntMap.add prog.max_term_hol (None, a) prog.prog}
    )

let get_fresh_type_hol prog =
    (Type.Hol prog.max_type_hol,
    {max_term_hol = prog.max_term_hol;
     max_type_hol = prog.max_type_hol + 1;
     current_term_hol = prog.current_term_hol;
     prog = prog.prog}
    )

let expand_current_hol m prog =
    {max_term_hol = prog.max_term_hol;
     max_type_hol = prog.max_type_hol;
     current_term_hol = prog.current_term_hol + 1;
     prog = IntMap.add prog.current_term_hol (Some m, Term.extract_label m) prog.prog}

(* TODO find a better name to avoid conflict with Lambda.apply_subst *)
let apply_subst subst prog =
    let apply_subst_to_pair subst p = match p with
    | (Some m, a) -> (Some (Term.map_label (apply_subst subst) m), apply_subst subst a)
    | (None, a) -> (None, apply_subst subst a) in

    {max_term_hol = prog.max_term_hol;
     max_type_hol = prog.max_type_hol;
     current_term_hol = prog.current_term_hol;
     prog = IntMap.map (apply_subst_to_pair subst) prog.prog}


(* TODO think which functions should be defined in this module,
 * for example eval or first program given a goal type or something like that *)

