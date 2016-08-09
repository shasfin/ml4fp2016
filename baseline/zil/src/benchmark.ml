open Core.Std;;

open Lambda;;
open Parse;;
open SyntaxSugar;;


type t = {
    name: string;
    goal_type: Type.t;
    examples: ((string list * string list) * string) list;
}


let append =
  let example (xs, ys) = (([list_to_intlist xs; list_to_intlist ys],["Int"]), list_to_intlist (List.append xs ys)) in

  {
   name = "append";
   goal_type = parse_type "@ List #0 -> List #0 -> List #0";
   examples = List.map ~f:example
                 [([1;2;3],[4;5]);
                  ([4;1],[1;2])];
  }


let concat =
  let example xss = (([list_to_list "(List Int)" list_to_intlist xss],["Int"]),  list_to_intlist (List.concat xss)) in

  {
   name = "concat";
   goal_type = parse_type "@ List (List #0) -> List #0";
   examples = List.map ~f:example
                 [[[2;3];[]];
                  [[1];[2;3]]];
  }


let drop =
  let example (n, xs) = (([number_to_int n; list_to_intlist xs],["Int"]), list_to_intlist (List.drop xs n)) in

  {
   name = "drop";
   goal_type = parse_type "@ Int -> List #0 -> List #0";
   examples = List.map ~f:example
                [(0,[0;2]);
                 (2,[0;1;2])];
  }


let droplast =
  let droplast xs = List.take xs ((List.length xs) - 1) in
  let example xs = (([list_to_intlist xs],["Int"]),  (list_to_intlist (droplast xs))) in

  {
   name = "droplast";
   goal_type = parse_type "@ List #0 -> List #0";
   examples = List.map ~f:example
                 [[1;2;3];
                  [4;2]];
  }


let dropmax =
  let dropmax xs =
    let max = (match (List.max_elt ~cmp:compare xs) with
         | Some m -> m
         | None -> invalid_arg "max of empty list") in 
    List.filter
      ~f:(fun x -> not (x = max))
      xs in

  let example xs = (([list_to_intlist xs],[]), list_to_intlist (dropmax xs)) in

  {
   name = "dropmax";
   goal_type = parse_type "List Int -> List Int";
   examples = List.map ~f:example
                 [[1;4;0];
                  [5;2]];
  }


let enumFromTo =
  let example (n, m) = (([number_to_int n; number_to_int m],[]),  list_to_intlist (List.range ~stop:`inclusive n m)) in
 
  {
   name = "enumFromTo";
   goal_type = parse_type "Int -> Int -> List Int";
   examples = List.map ~f:example
                 [(0,1);
                  (1,2);
                  (2,5)];
  }


let enumTo =
  let example x = (([number_to_int x],[]), list_to_intlist (List.range ~stop:`inclusive 1 x)) in

  {
   name = "enumTo";
   goal_type = parse_type "Int -> List Int";
   examples = List.map ~f:example
                 [2;
                  4];
  }


let factorial =
  let rec factorial = function
    | 0 | 1 -> 1
    | n when n > 1 -> n * (factorial (n-1))
    | _ -> invalid_arg "Argument to factorial must be positive" in

  let example x = (([number_to_int x],[]), number_to_int (factorial x)) in

  {
   name = "factorial";
   goal_type = parse_type "Int -> Int";
   examples = List.map ~f:example
                 [2;
                  4];
  }


let is_even =
  let example n = (([number_to_int n],[]), string_of_bool ((n mod 2) = 0)) in

  {
   name = "is_even";
   goal_type = parse_type "Int -> Bool";
   examples = List.map ~f:example
                [0;
                 1;
                 2];
  }


let is_nil =
  let example xs = (([list_to_intlist xs],["Int"]), string_of_bool (List.is_empty xs)) in

  {
   name = "is_nil";
   goal_type = parse_type "@ List #0 -> Bool";
   examples = List.map ~f:example
                [[];
                 [0;1;2]];
  }


let last =
  let example xs = (([list_to_intlist xs],["Int"]), number_to_int (List.last_exn xs)) in

  {
   name = "last";
   goal_type = parse_type "@ List #0 -> #0";
   examples = List.map ~f:example
                [[1;0;3];
                 [2;4]];
  }


let length =
  let example xs = (([list_to_intlist xs],["Int"]), number_to_int (List.length xs)) in

  {
   name = "length";
   goal_type = parse_type "@ List #0 -> Int";
   examples = List.map ~f:example
                [[0;2];
                 [1;1;0]]
  }


let map_add =
  let example (n, xs) = (([string_of_int n; list_to_intlist xs],[]),  list_to_intlist (List.map ~f:(fun x -> x + n) xs)) in

  {
   name = "map_add";
   goal_type = parse_type "Int -> List Int -> List Int";
   examples = List.map ~f:example
                [(1,[0]);
                 (3,[1;2])];
  }


let map_double =
  let example xs = (([list_to_intlist xs],[]), list_to_intlist (List.map ~f:(fun x
     -> x * 2) xs)) in

  {
   name = "map_double";
   goal_type = parse_type "List Int -> List Int";
   examples = List.map ~f:example
                [[1;0];
                 [1;1];
                 [1;2;3]];
  }


let maximum =
  let maximum xs = match List.max_elt ~cmp:compare xs with
      | Some m -> m
      | None -> invalid_arg "empty list" in 
  let example xs = (([list_to_intlist xs],[]),  number_to_int (maximum xs)) in

  {
   name = "maximum";
   goal_type = parse_type "List Int -> Int";
   examples = List.map ~f:example
                [[0;1];
                 [2;1];
                 [2;5;1]];
  }

    
let member =
  let example (x, xs) = (([string_of_int x; list_to_intlist xs],[]), string_of_bool (List.mem xs x)) in

  {
   name = "member";
   goal_type = parse_type "Int -> List Int -> Bool";
   examples = List.map ~f:example
                [(0, []); 
                 (1, []); 
                 (0, [0]); 
                 (1, [0;0]);
                 (1, [2;1]);
                 (2, [2;0;3]);
                 (2, [0;3;1])]
  }


let multfirst =
  let example xs = (([list_to_intlist xs],["Int"]), list_to_intlist (List.map ~f:(fun _ -> List.hd_exn xs) xs)) in

  {
   name = "multfirst";
   goal_type = parse_type "@ List #0 -> List #0";
   examples = List.map ~f:example
                [[0;2;3];
                 [4;2]];
  }


let multlast =
  let example xs = (([list_to_intlist xs],["Int"]), list_to_intlist (List.map ~f:(fun _ -> List.last_exn xs) xs)) in

  {
   name = "multlast";
   goal_type = parse_type "@ List #0 -> List #0";
   examples = List.map ~f:example
                [[1;0;3];
                 [4;2]];
  }


let nth =
    let example (n,xs) = (([number_to_int n; list_to_intlist xs],["Int"]), number_to_int (List.nth_exn xs (n-1))) in

  {
   name = "nth";
   goal_type = parse_type "@ Int -> List #0 -> #0";
   examples = List.map ~f:example
                [(1,[0]);
                 (2,[0;1;2]);
                 (1,[1;2;3])];
  }


let replicate =
  let example (x, n) = 
    let rec replicate n = match n with
      | 0 -> []
      | n -> x::(replicate (n-1)) in
      
      (([number_to_int x; number_to_int n],["Int"]), list_to_intlist (replicate n)) in

  {
   name = "replicate";
   goal_type = parse_type "@ #0 -> Int -> List #0";
   examples = List.map ~f:example
                [(1,0);
                 (0,2);
                 (3,1)];
  }


let reverse =
  let example xs = (([list_to_intlist xs],["Int"]), list_to_intlist (List.rev xs)) in

  {
   name = "reverse";
   goal_type = parse_type "@ List #0 -> List #0";
   examples = List.map ~f:example
                [[0;2;3];
                 [2;5;1]];
  }


let stutter =
  let rec stutter xs = (match xs with
      | [] -> []
      | x::xs -> x::x::(stutter xs)) in
  let example xs = (([list_to_intlist xs],["Int"]), list_to_intlist (stutter xs)) in

  {
   name = "stutter";
   goal_type = parse_type "@ List #0 -> List #0";
   examples = List.map ~f:example
                [[1];
                [1;2;3]];
  }


let sum =
  let example xs = (([list_to_intlist xs],[]),  number_to_int (List.fold_left ~f:(+) ~init:0 xs)) in

  {
   name = "sum";
   goal_type = parse_type "List Int -> Int";
   examples = List.map ~f:example
                [[1;5;0];
                 [4;2;1]];
  }


let take =
    let example (n, xs) = (([number_to_int n; list_to_intlist xs],["Int"]), list_to_intlist (List.take xs n)) in

  {
   name = "take";
   goal_type = parse_type "@ Int -> List #0 -> List #0";
   examples = List.map ~f:example
                [(0,[0;2]);
                 (2,[0;1;2])];
  }


let take_one = 
  let example xs = (([list_to_intlist xs],["Int"]), list_to_intlist (List.take xs 1)) in

  {
   name = "take_one";
   goal_type = parse_type "@ List #0 -> List #0";
   examples = List.map ~f:example
                [[0;2];
                 [0;2;1]]
  }


