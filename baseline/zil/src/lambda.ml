open Printf

(******************************************************************************)

type idx_sym = string

type idx_hol = int

type idx_free = int


(******************************************************************************)

module Kind = struct

  type t = int

end

(******************************************************************************)

module Type = struct

  type t =
    | Var of int
    | Arr of t * t
    | All of t
    | Sym of idx_sym * t list
    | Hol of idx_hol
    | Free of idx_free

  let rec to_string = function
    | Arr (a, b) -> sprintf "%s -> %s" (dom_to_string a) (to_string b)
    | All a      -> sprintf "@ %s" (to_string a)
    | a          -> dom_to_string a
  and dom_to_string = function
    | Sym (i, a::l) -> sprintf "%s %s" i (String.concat " " (List.map arg_to_string (a::l)))
    | a          -> arg_to_string a
  and arg_to_string = function
    | Sym (i, []) -> i
    | Var i       -> sprintf "#%d" i
    | Hol i       -> sprintf "^%d" i
    | Free i      -> sprintf "&%d" i
    | a           -> sprintf "(%s)" (to_string a)

  (* TODO think if you want normal equality or something more fancy taking "alpha conversion" into account *)
  let equal a b = (a = b)
  
  (* Substitute type subtree b instead of Var j in type a *)
  let rec subst b j a =
    match a with
	| Var i -> (if i = j then b else a)
	| Arr (a1, a2) -> Arr ((subst b j a1), (subst b j a2))
	| All (a) -> All (subst b (j+1) a)
	| Sym (i, l) -> Sym (i, List.map (subst b j) l)
	| _ -> a
	
end

(******************************************************************************)

module Term = struct

  type 'a t =
    | Var of 'a * int
    | App of 'a * 'a t * 'a t
    | Abs of 'a * Type.t * 'a t
    | APP of 'a * 'a t * Type.t
    | ABS of 'a * 'a t
    | Sym of 'a * idx_sym
    | Hol of 'a * idx_hol
    | Free of 'a * idx_free
    | Fun of 'a * 'a t * 'a env * 'a t option
    | FUN of 'a * 'a t * 'a env * 'a t option

  and 'a env = {
    type_stack: Type.t list;
    term_stack: 'a t list;
  }

  let rec to_string = function
    | Fun (_, _, _, Some m) -> to_string m
    | FUN (_, _, _, Some m) -> to_string m
    | ABS (_, m)            -> sprintf "* %s" (to_string m)
    | m                     -> cal_to_string m
  and cal_to_string = function
    | Fun (_, _, _, Some m) -> cal_to_string m
    | FUN (_, _, _, Some m) -> cal_to_string m
    | App (_, m, n)         -> sprintf "%s %s" (cal_to_string m) (arg_to_string n)
    | APP (_, m, a)         -> sprintf "%s %s" (cal_to_string m) (Type.arg_to_string a)
    | m                     -> arg_to_string m
  and arg_to_string = function
    | Fun (_, _, _, Some m) -> arg_to_string m
    | FUN (_, _, _, Some m) -> arg_to_string m
    | Fun (_, _, _, None)   -> "<fun>"
    | FUN (_, _, _, None)   -> "<FUN>"
    | Sym (_, i)            -> i
    | Var (_, i)            -> sprintf "$%d" i
    | Hol (_, i)            -> sprintf "?%d" i
    | Free (_, i)           -> sprintf "x%d" i
    | Abs (_, _, _) as m    -> abs_to_string m
    | m                     -> sprintf "(%s)" (to_string m)
  and abs_to_string m =
    let rec get_sig l = function
      | Abs (_, a, m) -> get_sig (a::l) m
      | m -> (List.rev l, m) in
    let l, m = get_sig [] m in
    sprintf "{ %s : %s }" (String.concat " " (List.map par_to_string l)) (to_string m)
  and par_to_string a = sprintf "[%s]" (Type.to_string a)

  let extract_label m =
    match m with
    | Var (a, _) -> a
    | App (a, _, _) -> a
    | Abs (a, _, _) -> a
    | APP (a, _, _) -> a
    | ABS (a, _) -> a
    | Sym (a, _) -> a
    | Hol (a, _) -> a
    | Free (a, _) -> a
    | Fun (a, _, _, _) -> a
    | FUN (a, _, _, _) -> a

end

(******************************************************************************)

open Term

type ('i, 'm, 't) lib = {
  type_info : 'i -> 't option;
  term_info : 'i -> 'm option;
}

let empty_env = {
  term_stack = [];
  type_stack = [];
}

let empty_lib = {
  type_info = (fun _ -> None);
  term_info = (fun _ -> None);
}

let empty_store = []
(* store is a stack of the types corresponding to the variables *)

let eval ?sym_def:(sym_def=empty_lib) ?hol_def:(hol_def=empty_lib) m =

  let load_term env m =
    match m with
    | Var (_, i) ->
      (try
         List.nth env.term_stack i
       with
         Failure _ -> m)
    | Sym (_, i) ->
      (match sym_def.term_info i with
       | Some m -> m | None -> m)
    | Hol (_, i) ->
      (match hol_def.term_info i with
       | Some m -> m | None -> m)
    | _ -> m in

  let load_type env a =
    match a with
    | Type.Var i ->
      (try
         List.nth env.type_stack i
       with
         Failure _ -> a)
    | Type.Hol i ->
      (match hol_def.type_info i with
       | Some a -> a | None -> a)
    | _ -> a in

  let rec eval_aux env alt m =
    match m with
    | App (o, m, n) ->
      let m = eval_aux env None m in
      let n = eval_aux env None n in
      (match m with
       | Fun (_, def, env, alt) ->
         let new_env = { env with term_stack = n::env.term_stack } in
         let new_alt =
           (match alt with
            | Some m -> Some (App (o, m, n)) | None -> None) in
         eval_aux new_env new_alt def
       | x -> App (o, m, n))

    | APP (o, m, a) ->
      let m = eval_aux env None m in
      let a = load_type env a in
      (match m with
       | FUN (_, def, env, alt) ->
         let new_env = { env with type_stack = a::env.type_stack } in
         let new_alt =
           (match alt with
            | Some m -> Some (APP (o, m, a))
            | None -> None) in
         eval_aux new_env new_alt def
       | x -> APP (o, m, a))

    | Abs (o, _, def) -> Fun (o, def, env, alt)
    | ABS (o, def)    -> FUN (o, def, env, alt)
    | m -> load_term env m in

  eval_aux empty_env None m

let name s = function
    | Fun (o, def, env, None) -> Fun (o, def, env, Some (Sym (o, s)))
    | FUN (o, def, env, None) -> FUN (o, def, env, Some (Sym (o, s)))
    | m -> m

let well ?sym_sig:(sym_sig=empty_lib) ?hol_sig:(hol_sig=empty_lib) ?free_sig:(free_sig=empty_lib) m =
  (* Reads the type of the term. Raises an exception if there is no type. *)
  let type_of m =
    let a = extract_label m in
    match a with
    | Some a -> a
    | None -> raise (Invalid_argument "Type not found") in


  (* Fills in the optional type information with None *)
  let rec none_term m = 
      match m with
    | Var (_, i) -> Var (None, i)
    | App (_, m, n) -> App (None, none_term m, none_term n)
    | Abs (_, a, m) -> Abs (None, a, none_term m)
    | APP (_, m, a) -> APP (None, m, a)
    | ABS (_, m) -> ABS (None, none_term m)
    | Sym (_, i) -> Sym (None, i)
    | Hol (_, i) -> Hol (None, i)
    | Free (_, i) -> Free (None, i)
    | Fun (_, def, env, alt) -> Fun (None, none_term def, env, alt)
    | FUN (_, def, env, alt) -> FUN (None, none_term def, env, alt) in


  (* Auxiliary function that actually makes all the work. Maintains a store, that is a stack of the types of the bound variables *)
  let rec well_aux store m =
    match m with
    | Var (_, i) -> 
      (try
        Var (Some (List.nth store i), i)
      with
        Failure _ -> raise (Invalid_argument "Unbound Var"))
    | App (_, m, n) ->
      let m = well_aux store m in
      let n = well_aux store n in
      let am = type_of m in
      let an = type_of n in
      (match am with
      | Type.Arr (a, b) ->
        (if Type.equal a an
        then App (Some b, m, n)
        else raise (Invalid_argument
          (sprintf "Cannot apply %s to %s as %s does not match %s"
            (Type.to_string am)
            (Type.to_string an)
            (Type.to_string a)
            (Type.to_string an)
          )))
      | _ -> raise (Invalid_argument
         (sprintf "Cannot apply type_of m = %s to type_of n = %s as %s is not an arrow type. m = %s and n = %s"
            (Type.to_string am)
            (Type.to_string an)
            (Type.to_string am)
            (to_string m)
            (to_string n)
         )))
    | Abs (_, a, m) ->
      let m = well_aux (a::store) m in
      let am = type_of m in
      Abs (Some (Type.Arr (a, am)), a, m)
    | APP (_, m, a) ->
      let m = well_aux store m in
      let am = type_of m in
      (match am with
      | Type.All b -> APP (Some (Type.subst a 0 b), m, a) (* TODO test if this is what you think it is *)
      | _ -> raise (Invalid_argument 
        (sprintf "Cannot apply %s to %s as %s is not a universal type"
          (Type.to_string a)
          (Type.to_string am)
          (Type.to_string am)
        )))
    | ABS (_, m) ->
      let m = well_aux store m in
      let am = type_of m in
      ABS (Some (Type.All am), m)
    | Sym (_, i) ->
      (match sym_sig.term_info i with
      | Some a -> Sym (Some a, i)
      | None -> raise (Invalid_argument (sprintf "Sym %s not found" i)))
    | Hol (_, i) ->
      (match hol_sig.term_info i with
      | Some a -> Hol (Some a, i)
      | None -> raise (Invalid_argument (sprintf "Hol %d not found" i)))
    | Free (_, i) ->
      (match free_sig.term_info i with
      | Some a -> Free (Some a, i)
      | None -> raise (Invalid_argument (sprintf "Free %d not found" i)))
    | Fun (_, def, env, alt) ->
      raise (Invalid_argument "not implemented") (* TODO think from where you can get T1 so that you can write the type as T1 -> type_of def *)
    | FUN (_, def, env, alt) ->
      raise (Invalid_argument "not implemented") (* TODO think about what arrow type should this be *)
  in
  well_aux empty_store m


        
