module Rewr where

open import Data.Bool
open import Data.Nat as N using (ℕ; zero; suc; _+_) renaming (_≟_ to _≟-Nat_)
open import Data.String using (String)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_) renaming (proj₁ to p1; proj₂ to p2)
open import Data.List using (List; []; _∷_; _++_; map; length)
open import Relation.Nullary.Decidable as Dec
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Reflection
open import Relation.Nullary using (Dec; yes; no)
open import Function using (_∘_)

--------------------------------------------------------------------------------
-- Error Handling

postulate
  error : ∀{a}{A : Set a} → String → A

--------------------------------------------------------------------------------
-- Some syntax sugaring

uncurry : ∀{a}{A B C : Set a} → (A → B → C) → A × B → C
uncurry f (a , b) = f a b

--------------------------------------------------------------------------------
-- Goal Manipulation

-- Utilities

argListMap : (Term → Term) → List (Arg Term) → List (Arg Term)
argListMap f = Data.List.map (argMap f)
  where
    argMap : (Term → Term) → Arg Term → Arg Term
    argMap f (arg i x) = arg i (f x)

-- maps a function over all variables. Usefull for manipulating
-- DeBruijn indexes.
{-# TERMINATING #-}
varMap : (ℕ → ℕ) → Term → Term
varMap f (var x args) = var (f x) (argListMap (varMap f) args)
varMap f (con c args) = con c (argListMap (varMap f) args)
varMap f (def d args) = def d (argListMap (varMap f) args)
varMap f (lam v t) = lam v (abs ? (varMap f ?))
varMap f (pat-lam cs args) = pat-lam cs (argListMap (varMap f) args)
varMap f (pi t₁ t₂) = pi t₁ t₂
varMap f (sort x) = sort x
varMap f (lit x) = lit x
varMap f unknown = unknown
-- TODO: why is the termination checker complaining?
--       the recursive calls are in structurally smaller args...

-- Remove argument information
unArg : {A : Set} → Arg A → A
unArg (arg _ x) = x

-- Transforms something into a visible relevant argument.
mkArgVR : {A : Set} → A → Arg A
mkArgVR x = arg (arg-info visible relevant) x

-- Some type synonyms
Implicits : Set
Implicits = List (Arg Term)

TermBuilder : Set
TermBuilder = Term → Term

-- Given something like "a ≡ b" will return
-- just (a × b × 'implicit parms').
-- If the top-most definition is not eq, though,
-- will return nothing.
un-≡ : Term → Maybe ((Term × Term) × Implicits)
un-≡ (def (quote _≡_) (i1 ∷ i2 ∷ a ∷ b ∷ []))
  = just ((unArg a , unArg b) , (i1 ∷ i2 ∷ []))
un-≡ _
  = nothing

-- Strips a common prefix of two lists.
--
-- > takeWith i j = a × b × c ⇔ a ++ b ≡ i ∧ a ++ c ≡ j
--
takeWith : ∀{a}{A : Set a} → (A → A → Bool) 
         → List A → List A → (List A × List A × List A)
takeWith f [] l2 = [] , [] , l2
takeWith f l1 [] = [] , l1 , []
takeWith f (x ∷ l1) (y ∷ l2) with f x y
...| true  = let a , b , c = takeWith f l1 l2 
             in x ∷ a , b , c
...| false = [] , (x ∷ l1) , (y ∷ l2)

-- Translates a Dec to a boolean, to be used with filters.
decToBool : ∀{a}{A : Set a}{x y : A} → Dec (x ≡ y) → Bool
decToBool (yes _) = true
decToBool (no  _) = false


-- Abstracts the common constructors of two terms.
-- 
-- > abstr "x ∷ (xs ++ [])" "x ∷ xs"
-- >   = "λ l → x ∷ l" × "xs ++ []" × "xs"
abstr : Term → Term → (Term × List Term × List Term)
abstr (con m am) (con n an) with (m ≟-Name n)
...| yes _ = let c , r1 , r2 = takeWith (λ x y → decToBool (x ≟-ArgTerm y)) am an 
             in con n c , Data.List.map unArg r1 , Data.List.map unArg r2
...| no  _ = unknown , con m am ∷ [] , con n an ∷ []
abstr m n  = unknown , m ∷ [] , n ∷ []

-- Given a constructor term, prepare a lambda abstraction by appending one variable to
-- the end of the given term argument list.
prepLambda : Term → Term
prepLambda (con n l)
  = let l' = argListMap (varMap suc) l
        a0 : List (Arg Term)
        a0 = mkArgVR (var 0 []) ∷ []
    in lam visible (abs ? (con n (l' ++ a0)))
prepLambda x
  = error "Cannot prepare a lambda on a non-constructor term"

-- Replicates a list of implicit parameters. UNUSED
repl : List (Arg Term) → List (Arg Term)
repl (a ∷ b ∷ []) = a ∷ a ∷ b ∷ b ∷ []
repl _            = error "unkown list of implicits" 

fromJust : ∀{a}{A : Set a} → Maybe A → A
fromJust (just a) = a
fromJust nothing  = error "fromJust"

-- The actual tactic
rewrWith′ : Term → Term → Term
rewrWith′ induc g with un-≡ g
...| just (a , i) = let l = prepLambda (p1 (uncurry abstr a))
                      in def (quote cong) (Data.List.map mkArgVR (l ∷ induc ∷ []))
...| nothing      = error "Not a _≡_ goal."

-------------------------------------------------------------------------------------
-- TESTING

++N : ∀{a}{A : Set a}(xs : List A)
      → xs ++ [] ≡ xs
++N []       = refl
++N (x ∷ xs) = tactic rewrWith′ (quoteTerm (++N xs))

++Assoc : ∀{a}{A : Set a}(xs ys zs : List A)
        → xs ++ (ys ++ zs) ≡ (xs ++ ys) ++ zs
++Assoc [] _ _         = refl
++Assoc (x ∷ xs) ys zs = tactic rewrWith′ (quoteTerm (++Assoc xs ys zs))

open import Data.Nat using (_≤_)

shouldFail : (n m : ℕ) → n ≤ m → suc n ≤ suc m
shouldFail zero m p = N.s≤s p
shouldFail (suc n) m p = {! tactic rewrWith′ (quoteTerm (shouldFail n m)) !}

---- Context testing

head : ∀{a}{A : Set a} → List A → A
head [] = error "Head"
head (x ∷ _) = x

ctxtest1 : ∀{a}{A : Set a} → ℕ → List A → A
ctxtest1 n l = ?
