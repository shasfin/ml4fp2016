open Printf

exception Undefined of string;;

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
    | Int

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
    | Int         -> "Int"
    | a           -> sprintf "(%s)" (to_string a)

  (* Simple type equality. A more fancy version is Lambda.type_equal *)
  let equal a b = (a = b)

  (* Substitute type subtree b instead of Var j in type a *)
  (* TODO take care of variable shifting. What if b itself contains some Vars that are bound in the outer context? *)
  let shift d a =
    let rec shift_aux c a =
      match a with
      | Var i -> if i < c then Var i else Var (i+d)
      | Arr (a, b) -> Arr (shift_aux c a, shift_aux c b)
      | All a -> All (shift_aux (c+1) a)
      | Sym (i, l) -> Sym (i, List.map (shift_aux c) l)
      | _ -> a
    in shift_aux 0 a

  let subst b j a =
    let rec subst_aux c a =
      match a with
    	| Var i -> (if i = j+c then (shift c b) else a)
    	| Arr (a1, a2) -> Arr ((subst_aux c a1), (subst_aux c a2))
    	| All a -> All (subst_aux (c+1) a)
    	| Sym (i, l) -> Sym (i, List.map (subst_aux c) l)
    	| _ -> a
    in subst_aux 0 a


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

   (* Substitutions *)
  type substitution = (idx_hol, t) Hashtbl.t

  let subst_to_string subst =
    Hashtbl.fold
      (fun i a acc -> sprintf " ^%d |-> %s, %s" i (to_string a) acc)
      subst
      ""

  let initial_guess = 10
  let empty_subst () = Hashtbl.create initial_guess

  let rec apply_subst subst a =
    match a with
    | Hol i -> if Hashtbl.mem subst i then apply_subst subst (Hashtbl.find subst i) else Hol i
    | Arr (a, b) -> Arr (apply_subst subst a, apply_subst subst b)
    | All a -> All (apply_subst subst a)
    | Sym (i, l) -> Sym (i, List.map (apply_subst subst) l)
    | _ -> a
  
end

(******************************************************************************)
(* Unification of types *)
open Type

(* Based on implementation from the book by Pierce *)
type constraint_set = (t * t) list

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
            (*(* TODO debugging *) let () = print_string (sprintf "...unifying %s with %s\n" (to_string a) (to_string (Hol i))) in
            let () = List.iter (fun (a1, a2) -> print_string (sprintf "    (%s, %s), " (to_string a1) (to_string a2))) (substinconstr i a constr) in 
            let () = print_string "...\n" in(* end *)*)
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
    | (Free i1, Free i2) :: constr ->
        if i1 = i2 then unify constr
        else raise (Invalid_argument (sprintf "Unsolvable constraints, cannot unify %s with %s"
            (to_string (Free i1))
            (to_string (Free i2))))
    | (Int, Int) :: constr -> unify constr
    | (a, b) :: constr -> raise (Invalid_argument (sprintf "Unsolvable constraints, cannot unify %s with %s"
			(to_string a)
			(to_string b))) (* Cannot unify input variables, bound variables and universal types, among other cases *)

(******************************************************************************)

type ('i, 'm, 't) lib = {
  type_info : 'i -> 't option;
  term_info : 'i -> 'm option;
}

let empty_lib = {
  type_info = (fun _ -> None);
  term_info = (fun _ -> None);
}

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
    | Int of 'a * int
    | Fun of 'a * 'a t * 'a env * 'a t option
    | FUN of 'a * 'a t * 'a env * 'a t option
    | BuiltinFun of 'a * (((idx_sym, unit t, Type.t) lib * unit t) -> unit t) * 'a t option

  and 'a env = {
    type_stack: Type.t list;
    term_stack: 'a t list;
  }

  let rec to_string ?debug:(debug=false) = function
    | Fun (_, _, _, Some m) -> if debug then sprintf "<<Fun %s>>" (to_string m) else to_string m
    | FUN (_, _, _, Some m) -> if debug then sprintf "<<FUN %s>>" (to_string m) else to_string m
    | BuiltinFun (_, _, Some m) -> if debug then sprintf "<<BuiltinFun %s>>" (to_string m) else to_string m
    | ABS (_, m)            -> sprintf "* %s" (to_string m)
    | m                     -> cal_to_string m
  and cal_to_string = function
    | Fun (_, _, _, Some m) -> cal_to_string m
    | FUN (_, _, _, Some m) -> cal_to_string m
    | BuiltinFun (_, _, Some m) -> cal_to_string m
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
    | Int (_, i)            -> sprintf "%d" i
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
    | Var  (o, _)          -> o
    | App  (o, _, _)       -> o
    | Abs  (o, _, _)       -> o
    | APP  (o, _, _)       -> o
    | ABS  (o, _)          -> o
    | Sym  (o, _)          -> o
    | Hol  (o, _)          -> o
    | Free (o, _)          -> o
    | Int  (o, _)          -> o
    | Fun  (o, _, _, _)    -> o
    | FUN  (o, _, _, _)    -> o
    | BuiltinFun (o, _, _) -> o

  let map_label f m =
    let rec map_label_aux m =
      let map_env env = {
        type_stack = env.type_stack;
        term_stack = List.map map_label_aux env.term_stack;
      } in
  
      let map_alt alt =
        (match alt with
        | Some m -> Some (map_label_aux m)
        | None -> None) in
           
      (match m with
      | Var  (o, i)             -> Var  (f o, i)
      | App  (o, m, n)          -> App  (f o, map_label_aux m, map_label_aux n)
      | Abs  (o, a, m)          -> Abs  (f o, a, map_label_aux m)
      | APP  (o, m, a)          -> APP  (f o, map_label_aux m, a)
      | ABS  (o, m)             -> ABS  (f o, map_label_aux m)
      | Sym  (o, i)             -> Sym  (f o, i)
      | Hol  (o, i)             -> Hol  (f o, i)
      | Free (o, i)             -> Free (f o, i)
      | Int  (o, i)             -> Int  (f o, i)
      | Fun  (o, def, env, alt) -> Fun  (f o, map_label_aux def, map_env env, map_alt alt)
      | FUN  (o, def, env, alt) -> FUN  (f o, map_label_aux def, map_env env, map_alt alt)
      | BuiltinFun (o, impl, alt) -> BuiltinFun (f o, impl, map_alt alt))

    in map_label_aux m

  let apply_subst subst m =
    let rec apply_subst_aux m =
      let apply_subst_env env = {
        type_stack = List.map (Type.apply_subst subst) env.type_stack;
        term_stack = List.map apply_subst_aux env.term_stack;
      } in

      let apply_subst_alt alt =
        match alt with
        | Some m -> Some (apply_subst_aux m)
        | None -> None in

      match m with
      | App (o, m, n) -> App (o, apply_subst_aux m, apply_subst_aux n)
      | Abs (o, a, m) -> Abs (o, Type.apply_subst subst a, apply_subst_aux m)
      | APP (o, m, a) -> APP (o, apply_subst_aux m, Type.apply_subst subst a)
      | ABS (o, m) -> ABS (o, apply_subst_aux m)
      | Fun (o, def, env, alt) -> Fun (o, apply_subst_aux def, apply_subst_env env, apply_subst_alt alt)
      | FUN (o, def, env, alt) -> FUN (o, apply_subst_aux def, apply_subst_env env, apply_subst_alt alt)
      | BuiltinFun (o, impl, alt) -> BuiltinFun (o, impl, apply_subst_alt alt)
      | _ -> m in

    apply_subst_aux m
end

(******************************************************************************)
open Term

let empty_env = {
  term_stack = [];
  type_stack = [];
}


let empty_store = []
(* store is a stack of the types corresponding to the variables *)

(* Expand a symbol type with its definition *)
let expand i l ?sym_def:(sym_def=empty_lib) ?sym_sig:(sym_sig=empty_lib) =
  let rec expand_aux a p l =
    (match l with
    | [] -> a
    | b::l -> expand_aux (subst b p a) (p-1) l) in
 
  let a = (match sym_def.type_info i with
    | Some a -> a
    | None -> invalid_arg (sprintf
      "Definition of type %s not found"
      i)) in
  let k = (match sym_sig.type_info i with
    | Some k -> k
    | None -> invalid_arg (sprintf
      "Signature of type %s not found"
      i)) in
  if List.length l > k
  then invalid_arg (sprintf
    "Too many arguments provided for type %s"
    i)
  else expand_aux a (k-1) l

let type_equal a b ?sym_def:(sym_def=empty_lib) ?sym_sig:(sym_sig=empty_lib)  =
  let rec equal a b =
    if (Type.to_string a = Type.to_string b) then true else
      (match a with
      | Type.Arr (a1, a2) ->
        (match b with
        | Type.Arr (b1, b2) -> (equal a1 b1) && (equal a2 b2)
        | Type.Sym (i, l) -> equal a (expand i l ~sym_def:sym_def ~sym_sig:sym_sig)
        | _ -> false)
      | Type.All a1 ->
        (match b with
        | Type.All b1 -> equal a1 b1
        | Type.Sym (i, l) -> equal a (expand i l ~sym_def:sym_def ~sym_sig:sym_sig)
        | _ -> false)
      | Type.Sym (i, l) -> equal (expand i l ~sym_def:sym_def ~sym_sig:sym_sig) b
      | _ -> false) in
  equal a b


let replicate list n =
    let rec prepend n acc x =
      if n = 0 then acc else prepend (n-1) (x :: acc) x in
    let rec aux acc = function
      | [] -> acc
      | h :: t -> aux (prepend n acc h) t  in
    (* This could also be written as:
       List.fold_left (prepend n) [] (List.rev list) *)
    aux [] (List.rev list);;

let eval ?debug:(debug=false) ?sym_def:(sym_def=empty_lib) ?hol_def:(hol_def=empty_lib) ?free_def:(free_def=empty_lib) m =
  let depth = ref 0 in

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
    | Type.Free i ->
      (match free_def.type_info i with
      | Some a -> a | None -> a)
    | _ -> a in

  let rec eval_aux env alt m =
 
    let () = if debug then print_endline (sprintf "%s-> %s" (String.concat "" (replicate ["  "] !depth)) (to_string ~debug:true m)) else () in

    match m with
    | App (o, m, n) ->

      let () = depth := !depth + 1 in

      let m = eval_aux env None m in

      let () = if debug then print_endline (sprintf "%s<- %s" (String.concat "" (replicate ["  "] !depth)) (to_string ~debug:true m)) else () in

      let n = eval_aux env None n in

      let () = if debug then print_endline (sprintf "%s<- %s" (String.concat "" (replicate ["  "] !depth)) (to_string ~debug:true n)) else () in

      let () = depth := !depth - 1 in

      (match m with
       | Fun (_, def, env, alt) ->
         let new_env = { env with term_stack = n::env.term_stack } in
         let new_alt =
           (match alt with
            | Some m -> Some (App (o, m, n)) | None -> None) in

         let () = depth := !depth + 1 in

         let r = eval_aux new_env new_alt def in

         let () = if debug then print_endline (sprintf "%s<- %s" (String.concat "" (replicate ["  "] !depth)) (to_string ~debug:true r)) else () in
         let () = depth := !depth - 1 in

         r

       | BuiltinFun (_, impl, alt) ->
         let new_env = { env with term_stack = n::env.term_stack } in
         let new_alt =
           (match alt with
            | Some m -> Some (App (o, m, n)) | None -> None) in

            let () = depth := !depth + 1 in

            let q = (try impl (sym_def, n) with
            | Undefined s ->
              let () = if debug then print_endline (sprintf "%s<- Exception undefined" (String.concat "" (replicate ["  "] !depth))) else () in
              let () = depth := !depth - 1 in
            raise (Undefined s)) in

            let r = eval_aux new_env new_alt q in

            let () = if debug then print_endline (sprintf "%s<- %s" (String.concat "" (replicate ["  "] !depth)) (to_string ~debug:true r)) else () in
            let () = depth := !depth - 1 in

            r

       | x -> App (o, m, n))

    | APP (o, m, a) ->

      let () = depth := !depth + 1 in

      let m = eval_aux env None m in
      let a = load_type env a in

      let () = if debug then print_endline (sprintf "%s<- %s" (String.concat "" (replicate ["  "] !depth)) (to_string ~debug:true m)) else () in
      
      let () = depth := !depth - 1 in

      (match m with
       | FUN (_, def, env, alt) ->
         let new_env = { env with type_stack = a::env.type_stack } in
         let new_alt =
           (match alt with
            | Some m -> Some (APP (o, m, a))
            | None -> None) in

         let () = depth := !depth + 1 in

         let r = eval_aux new_env new_alt def in

         let () = if debug then print_endline (sprintf "%s<- %s" (String.concat "" (replicate ["  "] !depth)) (to_string ~debug:true r)) else () in

         let () = depth := !depth - 1 in

         r

       | x -> APP (o, m, a))

    | Abs (o, _, def) -> Fun (o, def, env, alt)
    | ABS (o, def)    -> FUN (o, def, env, alt)
    | m -> load_term env m in

  let r = eval_aux empty_env None m in
  let () = if debug then print_endline (sprintf "<- %s" (to_string ~debug:true r)) else () in
  r

let name s = function
    | Fun (o, def, env, None) -> Fun (o, def, env, Some (Sym (o, s)))
    | FUN (o, def, env, None) -> FUN (o, def, env, Some (Sym (o, s)))
    | m -> m

let well ?sym_def:(sym_def=empty_lib) ?sym_sig:(sym_sig=empty_lib) ?hol_sig:(hol_sig=empty_lib) ?free_sig:(free_sig=empty_lib) m =

  let subst_top b a = shift (-1) (subst (shift 1 b) 0 a) in

  (* Reads the type of the term. Raises an exception if there is no type. *)
  let type_of m =
    let a = extract_label m in
    (match a with
    | Some a -> a
    | None -> invalid_arg (sprintf
      "Could not typecheck %s"
      (to_string m))) in

  (* Auxiliary function that actually makes all the work. Maintains a store, that is a stack of the types of the bound variables *)
  let rec well_aux store m =
    match m with
    | Var (_, i) -> 
      (try
        Var (Some (List.nth store i), i)
      with
        Failure _ -> invalid_arg "Unbound Var")

    | App (_, m, n) ->
      let m = well_aux store m in
      let n = well_aux store n in
      let am = type_of m in
      let an = type_of n in
      let typecheck_arr m n a b an =
        (if type_equal a an ~sym_def:sym_def ~sym_sig:sym_sig
        then App (Some b, m, n)
        else invalid_arg (sprintf
          "Cannot apply type_of m = %s to type_of n = %s as %s does not match %s. m = %s and n = %s"
          (Type.to_string am)
          (Type.to_string an)
          (Type.to_string a)
          (Type.to_string an)
          (to_string m)
          (to_string n))) in

      (match am with
      | Type.Arr (a, b) -> typecheck_arr m n a b an
      | Type.Sym (i, l) ->
        let am = expand i l ~sym_def:sym_def ~sym_sig:sym_sig in
         (match am with
         | Type.Arr (a, b) -> typecheck_arr m n a b an
         | _ -> invalid_arg (sprintf
           "Cannot apply type_of m = %s to type_of n = %s as %s is not an arrow type. m = %s and n = %s"
           (Type.to_string am)
           (Type.to_string an)
           (Type.to_string am)
           (to_string m)
           (to_string n)))
      | _ -> invalid_arg (sprintf 
        "Cannot apply type_of m = %s to type_of n = %s as %s is not an arrow type. m = %s and n = %s"
       (Type.to_string am)
       (Type.to_string an)
       (Type.to_string am)
       (to_string m)
       (to_string n)))

    | Abs (_, a, m) ->
      let m = well_aux (a::store) m in
      let am = type_of m in
      Abs (Some (Type.Arr (a, am)), a, m)

    | APP (_, m, a) ->
      let m = well_aux store m in
      let am = type_of m in
      (match am with
      | Type.All b -> APP (Some (subst_top a b), m, a)
      | Type.Sym (i, l) ->
        let am = expand i l ~sym_sig:sym_sig ~sym_def:sym_def in
        (match am with
        | Type.All b ->
          APP (Some (subst_top a b), m, a)
        | _ -> invalid_arg (sprintf
          "Cannot apply %s to %s as %s is not a universal type"
          (Type.to_string a)
          (Type.to_string am)
          (Type.to_string am)))
      | _ -> invalid_arg (sprintf
        "Cannot apply %s to %s as %s is not a universal type"
        (Type.to_string a)
        (Type.to_string am)
        (Type.to_string am)))

    | ABS (_, m) ->
      let m = well_aux (List.map (shift 1) store) m in
      let am = type_of m in
      ABS (Some (Type.All am), m)
    | Sym (_, i) ->
      (match sym_sig.term_info i with
      | Some a -> Sym (Some a, i)
      | None -> invalid_arg (sprintf "Sym %s not found" i))
    | Hol (_, i) ->
      (match hol_sig.term_info i with
      | Some a -> Hol (Some a, i)
      | None -> invalid_arg (sprintf "Hol %d not found" i))
    | Free (_, i) ->
      (match free_sig.term_info i with
      | Some a -> Free (Some a, i)
      | None -> invalid_arg (sprintf "Free %d not found" i))
    | Int (_, i) -> Int (Some Type.Int, i)
    | Fun (_, def, env, alt) -> invalid_arg "not implemented"
    | FUN (_, def, env, alt) -> invalid_arg "not implemented"
    | BuiltinFun (_, impl, alt) -> invalid_arg "not implemented"
  in
  well_aux empty_store m


let rec to_string_ignore_types = function
    | Term.Fun (_, _, _, Some m) -> to_string_ignore_types m
    | Term.FUN (_, _, _, Some m) -> to_string_ignore_types m
    | Term.BuiltinFun (_, _, Some m) -> to_string_ignore_types m
    | Term.ABS (_, m)            -> sprintf "* %s" (to_string_ignore_types m)
    | m                     -> cal_to_string m
  and cal_to_string = function
    | Term.Fun (_, _, _, Some m) -> cal_to_string m
    | Term.FUN (_, _, _, Some m) -> cal_to_string m
    | Term.BuiltinFun (_, _, Some m) -> cal_to_string m
    | Term.App (_, m, n)         -> sprintf "%s %s" (cal_to_string m) (arg_to_string n)
    | Term.APP (_, m, _)         -> sprintf "%s" (cal_to_string m)
    | m                     -> arg_to_string m
  and arg_to_string = function
    | Term.Fun (_, _, _, Some m) -> arg_to_string m
    | Term.FUN (_, _, _, Some m) -> arg_to_string m
    | Term.Fun (_, _, _, None)   -> "<fun>"
    | Term.FUN (_, _, _, None)   -> "<FUN>"
    | Term.Sym (_, i)            -> i
    | Term.Var (_, i)            -> "_" 
    | Term.Hol (_, i)            -> "_" 
    | Term.Free (_, i)           -> "_" 
    | Term.Int (_, i)            -> "_" 
    | Term.Abs (_, _, _) as m    -> abs_to_string m
    | m                     -> sprintf "(%s)" (to_string_ignore_types m)
  and abs_to_string m =
    let rec get_sig l = function
      | Term.Abs (_, a, m) -> get_sig (a::l) m
      | m -> (List.rev l, m) in
    let l, m = get_sig [] m in
    sprintf "{ %s : %s }" (String.concat " " (List.map par_to_string l)) (to_string_ignore_types m)
  and par_to_string a = sprintf "[%s]" (Type.to_string a) 
        
