open Printf
open Lambda
open Library

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
end
        
(******************************************************************************)

(* Prepare library for unification *)

(* Synthesise first program *)

(******************************************************************************)

open Program
(* Expand only one of the holes, the open hole with the smallest number. Returns a list of contexts *)
(* ctxt is of type Program.t *)
(* sym_sig and free_sig are hashtbls and already prepared for unification, their type holes are already included in ctxt.max_type_hol *)
let successor ctxt ~sym_lib:sym_lib ~free_lib:free_lib =
    let succ_app =
        let current_type = current_type ctxt in
        let (a0, new_ctxt) = get_fresh_type_hol ctxt in
        let (m1, new_ctxt) = get_fresh_term_hol (Type.Arr (a0, current_type)) new_ctxt in
        let (m2, new_ctxt) = get_fresh_term_hol a0 new_ctxt in
        let m = Term.App (current_type, m1, m2) in
        [expand_current_hol m new_ctxt]
    in

    let succ_free =
      List.map
        (fun (i, a, subst) ->
          let new_ctxt = expand_current_hol (Term.Free (a, i)) ctxt in
          apply_subst subst new_ctxt
        )
        (unifiable_term_sigs free_lib (current_type ctxt)) in
              
    let succ_sym =
      List.map
        (fun (i, a, subst) ->
          let new_ctxt = expand_current_hol (Term.Sym (a, i)) ctxt in
          apply_subst subst new_ctxt
        )
        (unifiable_term_sigs sym_lib (current_type ctxt)) in

    if Program.is_closed ctxt
    then []
    else succ_app @ succ_free @ succ_sym

(* Given a queue and the libraries (hashtables ready for unification), return the list of the first n closed programs found during BFS *)
let enumerate queue ~sym_lib:sym_lib ~free_lib:free_lib n =
    (* Queue is not a functional queue, that's why it is not an argument to find_first_closed *)
    let find_first_closed =
        while not (Program.is_closed (Queue.top queue)) do
            let s = successor (Queue.pop queue) ~sym_lib:sym_lib ~free_lib:free_lib in
            List.iter (fun x -> Queue.push x queue) s
        done;
        Queue.pop queue in

    let rec enumerate_aux i =
        (match i with
        | 0 -> []
        | _ -> find_first_closed :: (enumerate_aux (i-1)))

    in enumerate_aux n


(******************************************************************************)


(******************************************************************************)
