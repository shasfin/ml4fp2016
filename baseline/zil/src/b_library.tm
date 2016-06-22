-- Lines starting with '--' are comments
-- Lines starting with [a..z] are structured as 'idx_sym | term | type' and define terms in the library
-- Lines starting with [A..Z] are structured as 'idx_sym | type | kind' and define types in the library
-- Empty lines are ignored, all other lines should give an error

-- Use built-in integers instead of Nat

-- Types

-- Lists
List | @ #0 -> (#1 -> List #1 -> #0) -> #0 | 1

-- Booleans
Bool | @ #0 -> #0 -> #0 | 0

-- Pairs
Pair | @ (#2 -> #1 -> #0) -> #0 | 2

----------------------------------------------
-- Terms

-- general functions
const | * * { [#1] [#0] : $1 } | @ @ #1 -> #0 -> #1

flip | * * * { [#2 -> #1 -> #0] [#1] [#2] : $2 $0 $1 } | @ @ @ (#2 -> #1 -> #0) -> #1 -> #2 -> #0

curry | * * * { [Pair #2 #1 -> #0] : { [#2] [#1] : $2 (pair #2 #1 $1 $0) } } | @ @ @ (Pair #2 #1 -> #0) -> #2 -> #1 -> #0

uncurry | * * * { [#2 -> #1 -> #0] : { [Pair #2 #1] : $1 (fst #2 #1 $0) (snd #2 #1 $0) } } | @ @ @ (#2 -> #1 -> #0) -> Pair #2 #1 -> #0

fanout | * * * { [#2 -> #1] [#2 -> #0] [#2] : pair #1 #0 ($2 $0) ($1 $0) } | @ @ @ (#2 -> #1) -> (#2 -> #0) -> #2 -> Pair #1 #0

ignore | * * * { [#2 -> #1] [#2] [#0] : $2 $1 } | @ @ @ (#2 -> #1) -> #2 -> #0 -> #1

undefined | undefined | @ #0


-- list constructors
nil | * * { [#0] [#1 -> List #1 -> #0] : $1 } | @ List #0

con | * { [#0] [List #0] : * { [#0] [#1 -> List #1 -> #0] : $0 $3 $2 } } | @ #0 -> List #0 -> List #0

head | * { [List #0] : $0 #0 (undefined #0) { [#0] [List #0] : $1 } } | @ List #0 -> #0

tail | * { [List #0] : $0 (List #0) (undefined (List #0)) { [#0] [List #0] : $0 } } | @ List #0 -> List #0


-- bool constants
true | * { [#0] [#0] : $1 } | Bool

false | * { [#0] [#0] : $0 } | Bool


-- pair constructors
pair | * * { [#1] [#0] : * { [#2 -> #1 -> #0] : $0 $2 $1 } } | @ @ #1 -> #0 -> Pair #1 #0

fst | * * { [Pair #1 #0] : $0 #1 { [#1] [#0] : $1 } } | @ @ Pair #1 #0 -> #1

snd | * * { [Pair #1 #0] : $0 #0 { [#1] [#0] : $0 } } | @ @ Pair #1 #0 -> #0


-- list functions
map | * * {[#1 -> #0] [List #1] : $0 (List #0) (nil #0) {[#1] [List #1] : con #0 ($3 $1) (map #1 #0 $3 $0) } } | @ @ (#1 -> #0) -> List #1 -> List #0

foldr | * * { [#1 -> #0 -> #0] [#0] [List #1] : $0 #0 $1 { [#1] [List #1] : $4 $1 (foldr #1 #0 $4 $3 $0) } } | @ @ (#1 -> #0 -> #0) -> #0 -> List #1 -> #0

foldl | * * { [#1 -> #0 -> #1] [#1] [List #0] : $0 #1 $1 { [#0] [List #0] : foldl #1 #0 $4 ($4 $3 $1) $0 } } | @ @ (#1 -> #0 -> #1) -> #1 -> List #0 -> #1


-- list of int functions


sum | { [List Int] : $0 Int b_zero { [Int] [List Int] : b_add $1 (sum $0) } } | List Int -> Int

prod | { [List Int] : $0 Int 1 { [Int] [List Int] : b_mul $1 (prod $0) } } | List Int -> Int


-- implemented built-in functions. Just for documentation purposes

--b_zero | <<Built-in>> | Int
--b_succ | <<Built-in>> | Int -> Int

--b_foldNat | <<Built-in>> | @ (#0 -> #0) -> #0 -> Int -> #0
--b_foldNatNat | <<Built-in>> | @ (Int -> #0 -> #0) -> #0 -> Int -> #0

--b_add | <<Built-in>> | Int -> Int -> Int
--b_sub | <<Built-in>> | Int -> Int -> Int
--b_mul | <<Built-in>> | Int -> Int -> Int
--b_div | <<Built-in>> | Int -> Int -> Int
--b_max | <<Built-in>> | Int -> Int -> Int


-- derived (synthesized) functions using built-in int
length | * { [List #0] : foldr #0 Int (const (Int -> Int) #0 b_succ) b_zero $0 } | @ List #0 -> Int

factorial | { [Int] : b_foldNatNat Int b_mul 1 $0 } | Int -> Int

replicate | * { [Int] [#0] : b_foldNat (List #0) (con #0 $0) (nil #0) $1 } | @ Int -> #0 -> List #0

append | * { [List #0] [List #0] : foldr #0 (List #0) (con #0) $0 $1 } | @ List #0 -> List #0 -> List #0

rev | * { [List #0] : foldl (List #0) #0 (flip #0 (List #0) (List #0) (con #0)) (nil #0) $0 } | @ List #0 -> List #0

concat | * { [List (List #0)] : foldr (List #0) (List #0) (append #0) (nil #0) $0 } | @ List (List #0) -> List #0

enumTo | { [Int] : rev Int (b_foldNatNat (List Int) (con Int) (nil Int) $0) } | Int -> List Int

enumFromTo | { [Int] [Int] : con Int $1 (map Int Int (b_add $1) (enumTo (b_sub $0 $1))) } | Int -> Int -> List Int


