open Printf
open Core.Std
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

(******************************************************************************)
(* The successor function *)
(* Expand only one of the holes, the current open hole. Returns a list of contexts *)
(* ctxt is of type Program.t *)
(* sym_sig and free_sig are hashtbls and already prepared for unification, their type holes are already included in ctxt.max_type_hol *)
let successor ?debug:(debug=false) prog ~sym_lib:sym_lib ~free_lib:free_lib =
    
    let succ_app =
        let current_type = current_type prog in
        let (a0, new_prog) = get_fresh_type_hol prog in
        let (m2, new_prog) = get_fresh_term_hol a0 new_prog in
        let (m1, new_prog) = get_fresh_term_hol (Type.Arr (a0, current_type)) new_prog in
        let m = Term.App (current_type, m1, m2) in
        [expand_current_hol m new_prog]
    in

    let succ_free =
      List.map
        ~f:(fun (i, a, subst, _) ->
          let new_prog = expand_current_hol (Term.Free (a, i)) prog in
          apply_subst subst new_prog
        )
        (Library.unifiable_term_sigs free_lib (current_type prog)) in
    (*(* TODO debugging *) 
    let () = print_string (sprintf "Free terms unifying with %s:\n" (Type.to_string (current_type ctxt))) in
    let () = List.iter (fun (i, a, subst, _) -> print_string (sprintf "  %s :: %s\n     %s\n" (Term.to_string (Term.Free ((), i))) (Type.to_string a) (Type.subst_to_string subst))) (Library.unifiable_term_sigs free_lib (current_type ctxt)) in (* end *)*)
              
    let succ_sym =
      List.map
        ~f:(fun (i, a, subst, args) ->
          let new_type = universalise a args in
          let new_term = Term.Sym(new_type, i) in
          let new_prog = expand_current_hol (apply_args new_term a args) prog in
          apply_subst subst new_prog
        )
        (Library.unifiable_term_sigs sym_lib (current_type prog)) in
    (*(* TODO debugging *) 
    let () = print_string (sprintf "Sym terms unifying with %s:\n" (Type.to_string (current_type ctxt))) in
    let () = List.iter (fun (i, a, subst, _) -> print_string (sprintf "  %s :: %s\n     %s\n" (Term.to_string (Term.Sym ((), i))) (Type.to_string a) (Type.subst_to_string subst))) (Library.unifiable_term_sigs sym_lib (current_type ctxt)) in (* end *)*)


    if Program.is_closed prog
    then []
    else
        (let res = succ_free @ succ_sym @ succ_app in
        let () = if debug then List.iter ~f:(fun x -> print_string (sprintf "%s |-> %s \n %s\n|-> %s\n\n" (Program.to_string prog) (Program.to_string x) (Program.to_string_typed prog) (Program.to_string_typed x))) res else () in
        res)
 
(******************************************************************************)
(* Satisfying *)
(* I/O-examples are given as a pair of a free_def and a term *)

(* Does the given program satisfy the given I/O-example? *)
let satisfies_one ~sym_def m (free_def, output) =
    let output = Lambda.eval ~sym_def:sym_def ~free_def:free_def output in
    try (Lambda.eval ~sym_def:sym_def ~free_def:free_def m) = output with
    | Undefined s -> false
    | _ -> false

(* Does the given program satisfy all given I/O-examples? *)
let satisfies_all ~sym_def prog examples =
  (*let () = print_endline (sprintf "m = %s" (Program.to_string prog)) in*)
  List.for_all
    ~f:(fun (free_def, output) ->
      satisfies_one
       ~sym_def:sym_def
       (try (Program.eval ~sym_def:sym_def ~free_def:free_def prog) with
         | Undefined s -> Term.Sym ((), "undefined")
         | _ -> Term.Sym ((), "undefined"))
       (free_def, output))
    examples


let filter_satisfying progs examples ?sym_def:(sym_def=empty_lib) =
    List.filter ~f:(fun prog -> satisfies_all ~sym_def:sym_def prog examples) progs

(******************************************************************************)
(* Standard enumeration *)
(* Given a queue and the libraries (hashtables ready for unification), return the list of the first n closed programs found during BFS *)
let enumerate ?debug:(debug=false) queue ~sym_lib:sym_lib ~free_lib:free_lib n =
    let find_first_closed queue =
        while not (Program.is_closed (Heap.top_exn queue)) do
            let s = successor ~debug (Heap.pop_exn queue) ~sym_lib:sym_lib ~free_lib:free_lib in
            List.iter ~f:(fun x -> Heap.add queue x) s
        done;
        Heap.pop_exn queue in 

    let rec enumerate_aux i =
        (match i with
        | 0 -> []
        | _ -> (find_first_closed queue) :: (enumerate_aux (i-1)))

    in enumerate_aux n

(******************************************************************************)
(* Enumerate only satisfying programs (caution, could loop forever) *)

(* sym_lib is the library used for synthesis.
 * sym_def is a potentially fuller library used only for evaluation *)
let enumerate_satisfying ?debug:(debug=false) queue ~sym_lib ~free_lib ?sym_def:(sym_def=Library.get_lib_def sym_lib) ?examples:(examples=[]) n =
  
  let rec find_first_satisfying queue =

    let top = Heap.pop_exn queue in

    (if ((Program.is_closed top) && (satisfies_all ~sym_def:sym_def top examples))
     then top
     else 
       let s = successor ~debug top  ~sym_lib:sym_lib ~free_lib:free_lib in
        let (trues, falses) = List.partition_tf ~f:(fun x -> (Program.is_closed x) && (satisfies_all ~sym_def:sym_def x examples)) s in
        let () = List.iter ~f:(fun x -> Heap.add queue x) (List.filter ~f:(fun x -> not (Program.is_closed x)) falses) in
        (match trues with
        | [] -> find_first_satisfying queue
        | (p::ps) -> List.iter ~f:(fun x -> Heap.add queue x) ps; p)) in

  let rec enumerate_aux acc i =
      (match i with
      | 0 -> acc
      | _ -> 
        enumerate_aux ((find_first_satisfying queue)::acc) (i-1))
 
  in enumerate_aux [] n


(* version with timeout *)
let enumerate_satisfying_timeout ?debug:(debug=false) queue ~sym_lib ~free_lib ?sym_def:(sym_def=Library.get_lib_def sym_lib) ?examples:(examples=[]) max_lines =
  let lines = ref 0 in
  let rec find_first_satisfying queue =

    let top = Heap.pop_exn queue in

    (if ((Program.is_closed top) && (satisfies_all ~sym_def:sym_def top examples))
     then (Some top)
     else
       (if !lines >= max_lines then None
       else
        let s = successor ~debug top  ~sym_lib:sym_lib ~free_lib:free_lib in
        let () = lines := !lines + 4 * (List.length s) in
        let (trues, falses) = List.partition_tf ~f:(fun x -> (Program.is_closed x) && (satisfies_all ~sym_def:sym_def x examples)) s in
        let () = List.iter ~f:(fun x -> Heap.add queue x) (List.filter ~f:(fun x -> not (Program.is_closed x)) falses) in
        (match trues with
        | [] -> find_first_satisfying queue
        | (p::_) -> Some p))) in

find_first_satisfying queue

(******************************************************************************)
(* Enumerate satisfying programs (caution, could loop forever) *)
(* prune branches of the form App (o, m, ??) where m belongs to black_list *)

(* Does term m match the pattern n? *)
let rec matches (m, n) = match (m, n) with
  | (Term.App (_, m1, m2), Term.App (_, n1, n2)) -> (matches (m1, n1)) && (matches (m2, n2))
  | (_, Term.Hol _) -> true
  | (Term.Sym (_, i), Term.Sym (_, j)) -> i = j
  | (Term.Var (_, i), Term.Var (_, j)) -> i = j
  | (Term.Int (_, i), Term.Int (_, j)) -> i = j
  | (Term.Free (_, i), Term.Free (_, j)) -> i = j
  | (Term.Abs (_, _, m1), Term.Abs (_, _, n1)) -> matches (m1, n1)
  | (Term.APP (_, m1, _), Term.APP (_, n1, _)) -> matches (m1, n1)
  | (Term.ABS (_, m1), Term.ABS (_, n1)) -> matches (m1, n1)
  | _ -> false

(* Does any subtree of term m match the pattern n? *)
let matches_subtree m n =
  let rec subtree_aux m =
    matches (m, n) || (match m with
      | Term.App (_, m1, m2) -> (subtree_aux m1) || (subtree_aux m2)
      | Term.APP (_, m1, _) -> (subtree_aux m1)
      | Term.Abs (_, _, m1) -> (subtree_aux m1)
      | Term.ABS (_, m1) -> (subtree_aux m1)
      | _ -> false) in

  let res = subtree_aux m in

  (*let () = print_endline (sprintf
    "matches_subtree (%s) (%s) = %b"
    (Term.to_string m)
    (Term.to_string n)
    res) in*)

  res


(* black list on strings *)
(*let black_prog black_list prog =
  let str = to_string_ignore_types (to_term prog) in
  String.Set.exists black_list ~f:(fun x -> String.is_substring str ~substring:x)*)

(* black list on terms *)
let black_prog black_list prog =
  let m = to_term prog in
  List.exists black_list ~f:(fun x -> matches_subtree m x) 

let enumerate_with_black_list ?debug:(debug=false) queue ~sym_lib ~free_lib ~black_list ?sym_def:(sym_def=Library.get_lib_def sym_lib) ?examples:(examples=[]) n =
 
  let rec find_first_satisfying queue =

    let top = Heap.pop_exn queue in

    (if ((Program.is_closed top) && (satisfies_all ~sym_def:sym_def top examples))
    then top
    else
      (let s = successor ~debug top  ~sym_lib:sym_lib ~free_lib:free_lib in
      let (trues, falses) = List.partition_tf ~f:(fun x -> (Program.is_closed x) && (satisfies_all ~sym_def:sym_def x examples)) s in
      let () = List.iter ~f:(fun x -> Heap.add queue x) (List.filter ~f:(fun x -> not (Program.is_closed x) && not (black_prog black_list x))  falses) in
      (match trues with
      | [] -> find_first_satisfying queue
      | (p::ps) -> List.iter ~f:(fun x -> Heap.add queue x) ps; p))) in

  let rec enumerate_aux acc i =
      (match i with
      | 0 -> acc
      | _ -> 
        enumerate_aux ((find_first_satisfying queue)::acc) (i-1))
 
  in enumerate_aux [] n


(* version with timeout *)
let enumerate_with_black_list_timeout ?debug:(debug=false) queue ~sym_lib ~free_lib ~black_list ?sym_def:(sym_def=Library.get_lib_def sym_lib) ?examples:(examples=[]) max_lines =
  let lines = ref 0 in
  let rec find_first_satisfying queue =

    let top = Heap.pop_exn queue in

    (if ((Program.is_closed top) && (satisfies_all ~sym_def:sym_def top examples))
    then (Some top)
    else
      (if !lines >= max_lines then None
      else
        (let s = successor ~debug top  ~sym_lib:sym_lib ~free_lib:free_lib in
        let () = lines := !lines + 4 * (List.length s) in
        let (trues, falses) = List.partition_tf ~f:(fun x -> (Program.is_closed x) && (satisfies_all ~sym_def:sym_def x examples)) s in
        let () = List.iter ~f:(fun x -> Heap.add queue x) (List.filter ~f:(fun x -> not (Program.is_closed x) && not (black_prog black_list x))  falses) in
        (match trues with
        | [] -> find_first_satisfying queue
        | (p::_) -> Some p)))) in

find_first_satisfying queue

(******************************************************************************)
(* Enumeration with templates (does not loop forever, but can fail to find a satisfying program) *)
(* Enumerate templates with
 * nof_hoc higher-order components
 * nof_hol holes
 For each template, enumerate programs with the standard enumeration procedure using only first-order components, but call the standard enumeration procedure no more than nof_cal times *)
(* as always, sym_def is used only for evaluation *)
let enumerate_with_templates ?debug:(debug=false) queue ~higher_order_lib ~first_order_lib ~free_lib ~black_list ~sym_def ?examples:(examples=[]) ~nof_hoc ~nof_hol ~nof_cal =

  (*let rec is_first_order_type a = match a with
    | Type.All b -> false (* assume no universal types should be present *)
    | Type.Arr (a, b) -> (match a with
      | Type.All b -> false (* assume no universal types should be present *)
      | Type.Arr (a, b) -> false
      | _ -> is_first_order_type b)
    | _ -> true in*)

  let template_successor ?debug:(debug=false) (prog, n) =
    let succ_close prog =
      if (n <= nof_hoc && (Program.nof_holes prog) <= nof_hol) then
        [(Program.close_current_hol prog, n)]
      else [] in

    (* n = number of higher-order components in prog *)
    let succ_hoc prog n =
      if (n < nof_hoc && (Program.nof_holes prog) <= nof_hol) then
        List.map
        ~f:(fun (i, a, subst, args) ->
          let new_type = universalise a args in
          let new_term = Term.Sym(new_type, i) in
          let new_prog = expand_current_hol (apply_args new_term a args) prog in
          (apply_subst subst new_prog, n+1)
        )
        (Library.unifiable_term_sigs higher_order_lib (current_type prog))
      else [] in

    let succ_app prog =
      if ((Program.nof_holes prog) < nof_hol) then
        (let current_type = current_type prog in
        let (a0, new_prog) = get_fresh_type_hol prog in
        let (m2, new_prog) = get_fresh_term_hol a0 new_prog in
        let (m1, new_prog) = get_fresh_term_hol (Type.Arr (a0, current_type)) new_prog in
        let m = Term.App (current_type, m1, m2) in
        [(expand_current_hol m new_prog, n)])
      else [] in

    (if not (Program.is_closed prog) then
      let res = (succ_hoc prog n @ succ_close prog @ succ_app prog) in
      let () = (if debug then
        List.iter
          ~f:(fun (x, m) -> print_string
            (sprintf
              "(%s, %d) |-> (%s, %d) \n %s\n|-> %s\n\n"
              (Program.to_string prog)
              n
              (Program.to_string x)
              m
              (Program.to_string_typed prog)
              (Program.to_string_typed x)))
          res else ()) in
      res
    else []) in

  let first_order_enumerate_with_black_list prog =
    (*let () = print_endline (sprintf "|queue| = %d" (Heap.length queue)) in*)

    let cal = ref 0 in
    let queue = Heap.create () ~cmp:Program.compare in
    let () = Heap.add queue prog in

    let rec enumerate_aux queue =
      let () = (cal := !cal + 1) in
      (match Heap.pop queue with
      | Some top ->
      (if !cal > nof_cal then
        None
      else (if ((Program.is_closed top) && (satisfies_all ~sym_def:sym_def top examples)) then Some top
        else
          (let s = successor ~debug top  ~sym_lib:first_order_lib ~free_lib:free_lib in
          let (trues, falses) = List.partition_tf ~f:(fun x -> (Program.is_closed x) && (satisfies_all ~sym_def:sym_def x examples)) s in
          let () = List.iter ~f:(fun x -> Heap.add queue x) (List.filter ~f:(fun x -> not (Program.is_closed x) && not (black_prog black_list x))  falses) in
          (match trues with
          | [] -> enumerate_aux queue
          | (p::ps) -> List.iter ~f:(fun x -> Heap.add queue x) ps; Some p))))
      | None -> None) in
    
    enumerate_aux queue in

  let rec enumerate_templates template_queue =
    (*let () = print_endline (sprintf "|temp_queue| = %d" (Heap.length template_queue)) in*)
    (match Heap.pop template_queue with
    | Some (prog, n) ->
      (if (Program.nof_holes prog + n) > nof_hoc + nof_hol then
        enumerate_templates template_queue
      else if (Program.is_closed prog) then
        (match first_order_enumerate_with_black_list (Program.open_all_closed_holes prog) with
        | Some prog -> Some prog
        | None -> enumerate_templates template_queue)
      else
        (let s = template_successor ~debug (prog, n) in
         let () = List.iter
           ~f:(fun x -> Heap.add template_queue x)
           s in
          enumerate_templates template_queue))
    | None -> None)
    
    in

  enumerate_templates queue


