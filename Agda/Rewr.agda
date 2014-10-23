module Rewr where

open import Data.Nat as N using (ℕ; zero; suc; _+_)
open import Data.String using (String)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_) renaming (proj₁ to p1; proj₂ to p2)
open import Data.Bool using (Bool; if_then_else_)

open import Data.List using (List; []; _∷_; _++_)

open import Reflection
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable

--------------------------------------------------------------
-- * Applicative Maybe
--

infix 35 _<$>_
_<$>_ : ∀{a b}{A : Set a}{B : Set b}(f : A → B) → Maybe A → Maybe B
f <$> just x  = just (f x)
f <$> nothing = nothing

infixl 30 _<*>_
_<*>_ : ∀{a b}{A : Set a}{B : Set b} → Maybe (A → B) → Maybe A → Maybe B
just f  <*> m = f <$> m
nothing <*> m = nothing

--
---------------------------------------------------------------

-- Error Handling
postulate
  error : ∀{a}{A : Set a} → String → A

--------------------------------------------------------------
-- Term manipulation

-- Takes the term out of an el.
unEl : Type → Term
unEl (el _ x) = x

-- Takes the actual argument, ignoring argument info.
unArg : {A : Set} → Arg A → A
unArg (arg _ x) = x

-- Finds out whether or not we can rewrite something.
-- Receives a goal with the form "a ≡ b" and returns (a, b).
-- If the goal has no such form, returns nothing.
getEqTerms : Term → Maybe (Term × Term) 
getEqTerms g = {!p1!}

-- ok, we're modeling terms with the same constructor,
-- but we also need to strip some arguments.
--
-- x ∷ as and x ∷ bs have (_∷_ x) as a common prefix.
data ListDiff {a : Set} : List a → List a → List a → Set where
  eqNone : ∀{a b}     → ListDiff [] a b
  eqHead : ∀{a b c x} → ListDiff c (x ∷ a) (× ∷ b) → ListDiff (c ++ (x ∷ [])) a b

data TermDiff : Term → Term → Set where
  eqNone : ∀{m n}                                → TermDiff m n
  eqHead : ∀{a b c x y} → x ≡ y → ArgsDiff c a b → TermDiff (con x a) (con y b) 

-- Traverse both terms searching for a difference. Returns the
-- quoted common part and the two different terms.
--
-- > getDiff "x:(xs ++ ys)" "x:(ys ++ xs)"
-- >  = "x:", "(xs ++ ys)", "(ys ++ xs)"
--
getDiff : (n : Term) → (m : Term) → TermDiff m n
getDiff (con x a) (con y b) with (y ≟-Name x)
...| yes f = eqHead f
...| no  _ = eqNone 
getDiff n         m         = eqNone

++-t : ∀{a}{A : Set a}(xs ys : List A)(x : A)
     → x ∷ (xs ++ ys) ≡ x ∷ xs ++ ys
++-t xs ys x = {!getDiff (quoteTerm (x ∷ xs)) (quoteTerm (x ∷ ys))!}


