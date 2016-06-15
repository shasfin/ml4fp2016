open Printf
open Lambda

module IntMap = Map.Make(struct type t = int let compare = compare end)

type t = {
    max_term_hol: idx_hol; (* first fresh hole index *)
    max_type_hol: idx_hol; (* firse fresh type hole index *)
    open_holes: idx_hol list; (* stack of open holes *)
    prog: (Type.t Term.t option * Type.t) IntMap.t; (* mapping from term holes to terms and types *)
}

(* Create the empty program. Note that it is considered closed *)
let create () = {
    max_term_hol = 0;
    max_type_hol = 0;
    open_holes = [];
    prog = IntMap.empty;
}

(* Generate the first program consisting of a hole of a given type from an existing program. Only the information about used type holes is preserved *)
let reset prog a = {
    max_term_hol = 1;
    max_type_hol = prog.max_type_hol;
    open_holes = [0];
    prog = IntMap.add 0 (None, a) IntMap.empty;
}

let is_closed ctxt = (ctxt.open_holes = []) (* if there are no more holes to expand, the program is closed *)

let current_hol ctxt = List.hd ctxt.open_holes

let current_type ctxt = snd (IntMap.find (current_hol ctxt) ctxt.prog)

let get_fresh_term_hol a prog =
    (Term.Hol (a, prog.max_term_hol),
    {max_term_hol = prog.max_term_hol + 1;
     max_type_hol = prog.max_type_hol;
     open_holes = (List.hd prog.open_holes)::(prog.max_term_hol)::(List.tl prog.open_holes);
     prog = IntMap.add prog.max_term_hol (None, a) prog.prog}
    )

let get_fresh_type_hol prog =
    (Type.Hol prog.max_type_hol,
    {max_term_hol = prog.max_term_hol;
     max_type_hol = prog.max_type_hol + 1;
     open_holes = prog.open_holes;
     prog = prog.prog}
    )

let expand_current_hol m prog =
    {max_term_hol = prog.max_term_hol;
     max_type_hol = prog.max_type_hol;
     open_holes = List.tl prog.open_holes;
     prog = IntMap.add (current_hol prog) (Some m, Term.extract_label m) prog.prog}

(* TODO find a better name to avoid conflict with Lambda.apply_subst *)
let apply_subst subst prog =
    let apply_subst_to_pair subst p = match p with
    | (Some m, a) -> (Some (Term.map_label (Type.apply_subst subst) (Term.apply_subst subst m)), Type.apply_subst subst a)
    | (None, a) -> (None, Type.apply_subst subst a) in 

    {max_term_hol = prog.max_term_hol;
     max_type_hol = prog.max_type_hol;
     open_holes = prog.open_holes;
     prog = IntMap.map (apply_subst_to_pair subst) prog.prog}

let to_term prog =
  let rec to_term_i i =
      if i < prog.max_term_hol then
        (match (IntMap.find i prog.prog) with
        | (Some (Term.App (o, m1, m2)), _) -> Term.App (o, to_term_m m1, to_term_m m2)
        | (Some (Term.Abs (o, a, m)), _) -> Term.Abs (o, a, to_term_m m)
        | (Some (Term.APP (o, m, a)), _) -> Term.APP (o, to_term_m m, a)
        | (Some (Term.ABS (o, m)), _) -> Term.ABS (o, to_term_m m)
        | (Some (Term.Hol (o, j)), _) -> to_term_i j
        | (Some m, _) -> m
        | (None, a) -> Term.Hol (a, i))
      else
        raise (Invalid_argument (sprintf "Hol %d is not bound in the program" i))
  and to_term_m m =
    match m with
        | Term.App (o, m1, m2) -> Term.App (o, to_term_m m1, to_term_m m2)
        | Term.Abs (o, a, m) -> Term.Abs (o, a, to_term_m m)
        | Term.APP (o, m, a) -> Term.APP (o, to_term_m m, a)
        | Term.ABS (o, m) -> Term.ABS (o, to_term_m m)
        | Term.Hol (o, j) -> to_term_i j
        | _ -> m in
		
  to_term_i 0
	 
let to_string prog = Term.to_string (to_term prog)

let to_string_typed prog =
  IntMap.fold
    (fun i (_, a) acc -> sprintf "%s : %s, %s" (Term.to_string (Term.Hol ((), i))) (Type.to_string a) acc)
    prog.prog
    ""

let eval ?sym_def:(sym_def=empty_lib) ?hol_def:(hol_def=empty_lib) ?free_def:(free_def=empty_lib) prog =
  eval
    ~sym_def
	  ~hol_def
	  ~free_def
    (Term.map_label (fun _ -> ()) (to_term prog))
		
(* TODO think which functions should be defined in this module,
 * for example eval or first program given a goal type or something like that *)

let nof_nodes prog =
  let rec nof_nodes m = match m with
  | Term.Var _ -> 1
  | Term.Int _ -> 1
  | Term.App (_, m, n) -> 1 + (nof_nodes m) + (nof_nodes n)
  | Term.Abs (_, _, m) -> 1 + (nof_nodes m)
  | Term.APP (_, m, _) -> 1 + (nof_nodes m)
  | Term.ABS (_, m) -> 1 + (nof_nodes m)
  | Term.Sym _ -> 1
  | Term.Hol _ -> 2
  | Term.Free _ -> 0
  | Term.Fun (_, def, _, _) -> 2 + (nof_nodes def)
  | Term.FUN (_, def, _, _) -> 2 + (nof_nodes def)
  | Term.BuiltinFun _ -> 1

  in nof_nodes (to_term prog)
(* count holes double and don't count input variables *)

let nof_nodes_simple_type prog =
  let rec nof_type a = match a with
  | Type.Var _ -> 1
  | Type.Arr (a, b) -> 3 + (nof_type a) + (nof_type b)
  | Type.All a -> 1 + (nof_type a)
  | Type.Sym (_, l) -> 0 (* XXX you are ignoring the complexity of the argument types *)
  | Type.Hol _ -> 0
  | Type.Int -> 0
  | Type.Free _ -> 0 in

  let rec nof_nodes m = match m with
  | Term.Var _ -> 1
  | Term.App (_, m, n) -> 1 + (nof_nodes m) + (nof_nodes n)
  | Term.Abs (_, a, m) -> 1 + (nof_nodes m) + (nof_type a)
  | Term.APP (_, m, a) -> 1 + (nof_nodes m) + (nof_type a)
  | Term.ABS (_, m) -> 1 + (nof_nodes m)
  | Term.Int _ -> 1
  | Term.Sym _ -> 1
  | Term.Hol _ -> 2
  | Term.Free _ -> 0
  | Term.Fun (_, def, env, alt) -> 2 + (nof_nodes def)
  | Term.FUN (_, def, env, alt) -> 2 + (nof_nodes def)
  | Term.BuiltinFun _ -> 1

  in nof_nodes (to_term prog)
(* count holes double and don't count input variables, same for types, add the cost of the type to APP and Abs *)


let compare p1 p2 =
  (*p1.current_term_hol - p2.current_term_hol*)
  (* "Stupid queue" *)

  (*(nof_nodes_simple_type p1) - (nof_nodes_simple_type p2)*)
  (* Take also the size of types into account *)

  (nof_nodes p1) - (nof_nodes p2)
  (* Based on the number of nodes *)

  (*(p1.max_term_hol - p1.current_term_hol) - (p2.max_term_hol - p2.current_term_hol)*)
  (* Programs with less holes first *)

  (*p1.max_term_hol - p2.max_term_hol*)
  (* Number of used holes *)

  (*(p2.max_term_hol - p2.current_term_hol) - (p1.max_term_hol - p1.current_term_hol)*)
  (* Programs with more holes first - does not make any sense *)

  (*(p2.current_term_hol - p1.current_term_hol)*)
  (* inverse of the "stupid queue" - not good *)

  (*(match to_term p1 with
  | Term.App (_, Term.Sym _, _) -> (-1)
  | Term.APP (_, Term.Sym _, _) -> (-1)
  | _ -> (match to_term p2 with
    | Term.App (_, Term.Sym _, _) -> 1
    | Term.APP (_, Term.Sym _, _) -> 1
    | _ -> 0))*)
  (* Expand terms that start with some symbol first - slow because of to_term and not good *)

  (*String.length (to_string p1) - String.length (to_string p2)*)
  (* Shortest programs first - slow because of to_string *)


