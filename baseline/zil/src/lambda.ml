open Printf

(******************************************************************************)

type idx_sym = string

type idx_hol = int


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
    | a           -> sprintf "(%s)" (to_string a)

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
    | Abs (_, _, _) as m    -> abs_to_string m
    | m                     -> sprintf "(%s)" (to_string m)
  and abs_to_string m =
    let rec get_sig l = function
      | Abs (_, a, m) -> get_sig (a::l) m
      | m -> (List.rev l, m) in
    let l, m = get_sig [] m in
    sprintf "{ %s : %s }" (String.concat " " (List.map par_to_string l)) (to_string m)
  and par_to_string a = sprintf "[%s]" (Type.to_string a)

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

let well ?sym_sig:(sym_sig=empty_lib) ?hol_sig:(hol_sig=empty_lib) m = invalid_arg "not implemented"
