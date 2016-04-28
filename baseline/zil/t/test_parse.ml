open TestSimple;;

open Zil.Lambda;;
open Zil.Parse;;

plan 10;;

(**********************************************************)
(* Testing type parsing *)

let named_type = parse_type "Foo" in
is (Type.to_string named_type) "Foo" "parse named type";;

let type_variable = parse_type "#0" in
is (Type.to_string type_variable) "#0" "parse type variable";;

let type_hole = parse_type "^0" in
is (Type.to_string type_hole) "^0" "parse type hole";;

let type_free = parse_type "&0" in
is (Type.to_string type_free) "&0" "parse type free";;

let arrow_type = parse_type "#1 -> #0" in
is (Type.to_string arrow_type) "#1 -> #0" "parse arrow type";;

let forall_type = parse_type "@ #1 -> #0" in
is (Type.to_string forall_type) "@ #1 -> #0" "forall arrow type";;

let church_natural_type = parse_type "@ #0 -> (#0 -> #0) -> #0" in
is (Type.to_string church_natural_type) "@ #0 -> (#0 -> #0) -> #0" "parse church's natural type";;

let church_list_type = parse_type "@ #0 -> (#1 -> #0 -> #0) -> #0" in
is (Type.to_string church_list_type) "@ #0 -> (#1 -> #0 -> #0) -> #0" "parse church's list type";;

let map_type = parse_type "@ @ (#1 -> #0) -> List #1 -> List #0" in
is (Type.to_string map_type) "@ @ (#1 -> #0) -> List #1 -> List #0" "parse map's type";;

let length_type = parse_type "@ List #0 -> Int" in
is (Type.to_string length_type) "@ List #0 -> Int"  "parse length's type";;

let mixed_type = parse_type "@ @ (#1 -> ((^0) -> (#10)) -> Foo) -> List #1 -> List ^0" in
is (Type.to_string mixed_type) "@ @ (#1 -> (^0 -> #10) -> Foo) -> List #1 -> List ^0"  "parse a type with mixed subterms";;


(* TODO test that parsing fails on bad inputs *)

(**********************************************************)
(* Testing term parsing *)
(* TODO add more tests *)

let term_free = parse_term "_0" in
is (Term.to_string term_free) "_0" "parse term free";;
