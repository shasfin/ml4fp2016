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
  (* TODO take care of variable shifting. What if b itself contains some Vars that are bound in the outer context? *)
  let rec subst b j a =
    let rec shift c d a =
      match a with
      | Var i -> if i < c then Var i else Var (i+d)
      | Arr (a, b) -> Arr (shift c d a, shift c d b)
      | All a -> All (shift (c+1) d a)
      | Sym (i, l) -> Sym (i, List.map (shift c d) l)
      | _ -> a
    in
  match a with
	| Var i -> (if i = j then b else a)
	| Arr (a1, a2) -> Arr ((subst b j a1), (subst b j a2))
	| All (a) -> All (subst (shift 0 1 b) (j+1) a)
	| Sym (i, l) -> Sym (i, List.map (subst b j) l)
	| _ -> a


  (* Substitute type substree b in Hol j in type a *)
  let rec subst_hol b j a =
    match a with
    | Hol i -> if (i=j) then b else Hol i
    | Arr (a1, a2) -> Arr (subst_hol b j a1, subst_hol b j a2)
    | All a -> All (subst_hol b j a)
    | Sym (i, l) -> Sym (i, List.map (subst_hol b j) l)
    | _ -> a

  (* Substitute a variable iv instead of hole ih in type a *)
  let rec subst_var_in_hol iv ih a =
    match a with
    | All b -> All (subst_var_in_hol (iv+1) ih b)
    | Arr (a, b) -> Arr (subst_var_in_hol iv ih a, subst_var_in_hol iv ih b)
    | Sym (i, l) -> Sym (i, List.map (subst_var_in_hol iv ih) l)
    | Hol i -> if i = ih then Var iv else Hol i
    | _ -> a

end

(******************************************************************************)
(* Unification of types *)
open Type

type substitution = (idx_hol, t) Hashtbl.t
type constraint_set = (t * t) list

let subst_to_string subst =
  Hashtbl.fold
    (fun i a acc -> sprintf " ^%d |-> %s, %s" i (Type.to_string a) acc)
    subst
    ""

let initial_guess = 10
let empty_subst () = Hashtbl.create initial_guess

let rec apply_subst subst a =
    match a with
    | Hol i -> if Hashtbl.mem subst i then Hashtbl.find subst i else Hol i
    | Arr (a, b) -> Arr (apply_subst subst a, apply_subst subst b)
    | All a -> All (apply_subst subst a)
    | Sym (i, l) -> Sym (i, List.map (apply_subst subst) l)
    | _ -> a


(* Based on implementation from the book by Pierce *)
(* check if Hol j occurs in type a *)
let occursin j a =
    let rec occursin_aux a =
        match a with
        | Hol i -> (i=j)
        | Arr (a,b) -> occursin_aux a || occursin_aux b
        | All a -> occursin_aux a
        | Sym (i, l) -> List.fold_left (||) false (List.map occursin_aux l)
        | _ -> false
    in occursin_aux a

(* Substitute type a instead of Hol j in all types present in the list of constraints *)
let substinconstr j a constr =
    List.map (fun (b1, b2) -> (subst_hol a j b1, subst_hol a j b2)) constr


(* Unify a set of constraints. Unification of universal types is not implemented, transform universal types into types with holes before using this function. *)
let rec unify constr =
    match constr with
    | [] -> empty_subst ()
    | (a, Hol i) :: constr ->
        if a = Hol i then unify constr
        else if occursin i a then
            raise (Invalid_argument (sprintf "Circular constraints, %s occurs in %s"
                (to_string (Hol i))
                (to_string a)))
        else
            (* TODO debugging *) let () = print_string (sprintf "...unifying %s with %s\n" (to_string a) (to_string (Hol i))) in
            let () = List.iter (fun (a1, a2) -> print_string (sprintf "    (%s, %s), " (to_string a1) (to_string a2))) (substinconstr i a constr) in 
            let () = print_string "...\n" in(* end *)
            let subst = unify (substinconstr i a constr) in
            let () = Hashtbl.replace subst i a
            in subst
    | (Hol i, a) :: constr ->
        if a = Hol i then unify constr
        else if occursin i a then
            raise (Invalid_argument (sprintf "Circular constraints, %s occurs in %s"
                (to_string (Hol i))
                (to_string a)))
        else
            let subst = unify (substinconstr i a constr) in
            let () = Hashtbl.replace subst i a
            in subst
    | (Arr (a1, b1), Arr (a2, b2)) :: constr -> unify ((a1, a2) :: (b1, b2) :: constr)
    | (Sym (i1, l1), Sym (i2, l2)) :: constr ->
        if i1 = i2 then
            unify (List.append (List.combine l1 l2) constr)
        else raise (Invalid_argument (sprintf "Names do not agree, cannot unify %s with %s"
            (to_string (Sym (i1, l1)))
            (to_string (Sym (i2, l2)))))
    | (a, b) :: constr -> raise (Invalid_argument (sprintf "Unsolvable constraints, cannot unify %s with %s"
			(to_string a)
			(to_string b))) (* Cannot unify input variables, bound variables and universal types, among other cases *)

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
    | Free (_, i)           -> sprintf "_%d" i
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
    | Var  (o, _)       -> o
    | App  (o, _, _)    -> o
    | Abs  (o, _, _)    -> o
    | APP  (o, _, _)    -> o
    | ABS  (o, _)       -> o
    | Sym  (o, _)       -> o
    | Hol  (o, _)       -> o
    | Free (o, _)       -> o
    | Fun  (o, _, _, _) -> o
    | FUN  (o, _, _, _) -> o


  let rec map_label f m =
    let map_env env = {
      type_stack = env.type_stack;
      term_stack = List.map (map_label f) env.term_stack;
    } in

    let map_alt alt =
      match alt with
      | Some m -> Some (map_label f m)
      | None -> None in
         
    match m with
    | Var  (o, i)             -> Var  (f o, i)
    | App  (o, m, n)          -> App  (f o, map_label f m, map_label f n)
    | Abs  (o, a, m)          -> Abs  (f o, a, map_label f m)
    | APP  (o, m, a)          -> APP  (f o, map_label f m, a)
    | ABS  (o, m)             -> ABS  (f o, map_label f m)
    | Sym  (o, i)             -> Sym  (f o, i)
    | Hol  (o, i)             -> Hol  (f o, i)
    | Free (o, i)             -> Free (f o, i)
    | Fun  (o, def, env, alt) -> Fun  (f o, map_label f def, map_env env, map_alt alt)
    | FUN  (o, def, env, alt) -> FUN  (f o, map_label f def, map_env env, map_alt alt)
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

let eval ?sym_def:(sym_def=empty_lib) ?hol_def:(hol_def=empty_lib) ?free_def:(free_def=empty_lib) m =

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
    | Free (_, i) ->
      (match free_def.term_info i with
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


        
