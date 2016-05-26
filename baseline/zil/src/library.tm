-- Lines starting with '--' are comments
-- Lines starting with [a..z] are structured as 'idx_sym | term | type' and define terms in the library
-- Lines starting with [A..Z] are structured as 'idx_sym | type | kind' and define types in the library
-- Empty lines are ignored, all other lines should give an error

-- Types

-- Lists
List | @ #0 -> (#1 -> List #1 -> #0) -> #0 | 1

-- Natural numbers
Nat | @ #0 -> (Nat -> #0) -> #0 | 0


----------------------------------------------
-- Terms

-- general functions
const | * * { [#1] [#0] : $1 } | @ @ #1 -> #0 -> #1

flip | * * * { [#2 -> #1 -> #0] [#1] [#2] : $2 $0 $1 } | @ @ @ (#2 -> #1 -> #0) -> #1 -> #2 -> #0


-- list constructors
nil | * * { [#0] [#1 -> List #1 -> #0] : $1 } | @ List #0

con | * { [#0] [List #0] : * { [#0] [#1 -> List #1 -> #0] : $0 $3 $2 } } | @ #0 -> List #0 -> List #0



-- nat constructors
zero | * { [#0] [Nat -> #0] : $1 } | Nat

succ | { [Nat] : * { [#0] [Nat -> #0] : $0 $2 } } | Nat -> Nat



-- list functions
map | * * { [#1 -> #0] [List #1] : $0 #0 (nil #0) { [#1] [List #1] : con #0 ($3 $1) (map #1 #0 $3 $0) } } | @ @ (#1 -> #0) -> List #1 -> List #0

foldr | * * { [#1 -> #0 -> #0] [#0] [List #1] : $0 #0 $1 { [#1] [List #1] : $4 $1 (foldr #1 #0 $4 $3 $0) } } | @ @ (#1 -> #0 -> #0) -> #0 -> List #1 -> #0

foldl | * * { [#1 -> #0 -> #1] [#1] [List #0] : $0 #1 $1 { [#0] [List #0] : foldl #1 #0 $4 ($4 $3 $1) $0 } } | @ @ (#1 -> #0 -> #1) -> #1 -> List #0 -> #1



-- list of nat functions

sum | { [List Nat] : $0 Nat zero { [Nat] [List Nat] : add $1 (sum $0) } } | List Nat -> Nat


-- nat functions

add | { [Nat] [Nat] : $1 Nat $0 { [Nat] : succ (add $0 $1) } } | Nat -> Nat -> Nat

