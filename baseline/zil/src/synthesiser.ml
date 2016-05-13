open Printf
open Lambda
open Program

(******************************************************************************)
(* Prepare library for unification *)

(* args has the reversed order, i.e. for map A B we will get [B,A] *)
let rec deuniversalise a args ctxt = match a with
  | Type.All a ->
    let (a0, ctxt) = get_fresh_type_hol ctxt in
    let b = Type.subst a0 0 a in
    deuniversalise b (a0 :: args) ctxt
  | _ -> (a, args, ctxt)


(* args has the reversed order, i.e. for map A B we will have [B, A] in args *)
let rec universalise a args = match args with
  | [] -> a
  | (a0 :: args) ->
    (match a0 with
      | Type.Hol i ->
        let b = Type.All (Type.subst_var_in_hol 0 i a) in
        universalise b args
      | _ -> raise (Invalid_argument
        (sprintf
          "Cannot reconstruct universal type, as the argument %s is not a type hole"
          (Type.to_string a0))))

(* val prepare_lib : ('i, 'a) Library.t -> Program.t -> (('i,'a) Library.t * Program.t) *)
let prepare_lib lib ctxt =
  let new_lib = Library.create () in
  let () =
    Library.fold_types
      (fun i a k acc -> Library.add_type i a k new_lib)
      lib
      () in
  let new_ctxt =
    Library.fold_terms
      (fun i m a args ctxt ->
        let (a, args, ctxt) = deuniversalise a args ctxt in
        let () = Library.add_term i m a ~typ_args:args new_lib in
        ctxt)
      lib
      ctxt in
  (new_lib, new_ctxt)

(******************************************************************************)
(* Standard enumeration *)

(* Expand only one of the holes, the open hole with the smallest number. Returns a list of contexts *)
(* ctxt is of type Program.t *)
(* sym_sig and free_sig are hashtbls and already prepared for unification, their type holes are already included in ctxt.max_type_hol *)
let successor ctxt ~sym_lib:sym_lib ~free_lib:free_lib =

    (* args has the reversed order, i.e. for map A B we will have [B,A] *)
  let rec apply_args m a args = match args with
    | [] -> m
    | (a0 :: args) ->
      (match a0 with
      | Type.Hol i -> 
        let new_type = Type.All (Type.subst_var_in_hol 0 i a) in
        let new_term = apply_args m new_type args in
        Term.APP (a, new_term, a0)
      | _ -> raise (Invalid_argument
        (sprintf
          "Cannot reconstruct universal type, as the argument %s is not a type hole"
          (Type.to_string a0))))
  in
    
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
        (fun (i, a, subst, _) ->
          let new_ctxt = expand_current_hol (Term.Free (a, i)) ctxt in
          apply_subst subst new_ctxt
        )
        (Library.unifiable_term_sigs free_lib (current_type ctxt)) in
              
    let succ_sym =
      List.map
        (fun (i, a, subst, args) ->
          let new_type = universalise a args in
          let new_term = Term.Sym(new_type, i) in
          let new_ctxt = expand_current_hol (apply_args new_term a args) ctxt in
          apply_subst subst new_ctxt
        )
        (Library.unifiable_term_sigs sym_lib (current_type ctxt)) in

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

