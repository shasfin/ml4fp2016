-- Lines starting with '--' are comments
-- Lines starting with [a..z] are structured as 'idx_sym | term | type' and define terms in the library
-- Lines starting with [A..Z] are structured as 'idx_sym | type | kind' and define types in the library
-- Empty lines are ignored, all other lines should give an error

-- Types

-- Lists
List | @ #0 -> (#1 -> List #1 -> #0) -> #0 | 1

-- Natural numbers
Nat | @ #0 -> (Nat -> #0) -> #0 | 0

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


-- nat constructors
zero | * { [#0] [Nat -> #0] : $1 } | Nat

succ | { [Nat] : * { [#0] [Nat -> #0] : $0 $2 } } | Nat -> Nat


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


-- list of nat functions

range | { [Nat] [Nat] : sub (succ $0) $1 (List Nat) (nil Nat) { [Nat] : (con Nat $2 (range (succ $2) $1)) } } | Nat -> Nat -> List Nat

sum | { [List Nat] : $0 Nat zero { [Nat] [List Nat] : add $1 (sum $0) } } | List Nat -> Nat

prod | { [List Nat] : $0 Nat (succ zero) { [Nat] [List Nat] : mul $1 (prod $0) } } | List Nat -> Nat


-- nat functions

foldNat | * { [#0 -> #0] [#0] [Nat] : $0 #0 $1 { [Nat] : $3 (foldNat #0 $3 $2 $0) } } | @ (#0 -> #0) -> #0 -> Nat -> #0

natEq | { [Nat] [Nat] : $1 Bool ($0 Bool true { [Nat] : false } ) { [Nat] : $1 Bool false { [Nat] : natEq $1 $0 } } } | Nat -> Nat -> Bool

natGeq | { [Nat] [Nat] : $1 Bool ($0 Bool true { [Nat] : false } ) { [Nat] : $1 Bool true { [Nat] : natGeq $1 $0 } } } | Nat -> Nat -> Bool

sub | { [Nat] [Nat] : $1 Nat (zero) { [Nat] : $1 Nat $2 { [Nat] : sub $1 $0 } } } | Nat -> Nat -> Nat

add | { [Nat] [Nat] : $1 Nat $0 { [Nat] : succ (add $0 $1) } } | Nat -> Nat -> Nat

mul | { [Nat] [Nat] : $1 Nat zero { [Nat] : add (mul $0 $1) $1 } } | Nat -> Nat -> Nat


-- derived (synthesized) functions using built-in int
fast_length | * { [List #0] : foldr #0 Int (const (Int -> Int) #0 b_succ) b_zero $0 } | @ List #0 -> Int




-- derived (synthesized) functions using nat
length | * { [List #0] : foldr #0 Nat (const (Nat -> Nat) #0 succ) zero $0 } | @ List #0 -> Nat

factorial | { [Nat] : prod (range (succ zero) $0) } | Nat -> Nat

replicate | * { [Nat] [#0] : foldNat (List #0) (con #0 $0) (nil #0) $1 } | @ Nat -> #0 -> List #0

append | * { [List #0] [List #0] : foldr #0 (List #0) (con #0) $0 $1 } | @ List #0 -> List #0 -> List #0

rev | * { [List #0] : foldl (List #0) #0 (flip #0 (List #0) (List #0) (con #0)) (nil #0) $0 } | @ List #0 -> List #0

concat | * { [List (List #0)] : foldr (List #0) (List #0) (append #0) (nil #0) $0 } | @ List (List #0) -> List #0

enumTo | { [Nat] : rev Nat (snd Nat (List Nat) (pair_reverse_enum $0)) } | Nat -> List Nat

-- special function needed to synthesize enumTo with foldNat
f_enumTo | { [Pair Nat (List Nat)] : pair Nat (List Nat) (succ (fst Nat (List Nat) $0)) (uncurry Nat (List Nat) (List Nat) (con Nat) $0) } | Pair Nat (List Nat) -> Pair Nat (List Nat)

-- special function needed to synthesize enumTo with rev and snd
pair_reverse_enum | { [Nat] : foldNat (Pair Nat (List Nat)) f_enumTo (pair Nat (List Nat) (succ zero) (nil Nat)) $0 } | Nat -> Pair Nat (List Nat)
