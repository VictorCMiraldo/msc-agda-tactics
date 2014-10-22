module Rewr where

open import Data.Nat as N using (ℕ; zero; suc; _+_)
open import Data.String using (String)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_) renaming (proj₁ to p1; proj₂ to p2)

open import Reflection
open import Relation.Binary.PropositionalEquality


-- Error Handling
postulate
  error : ∀{a}{A : Set a} → String → A

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

-- Traverse both terms searching for a difference. Returns the
-- quoted common part and the two different terms.
--
-- > getDiff "x:(xs ++ ys)" "x:(ys ++ xs)"
-- >  = "x:", "(xs ++ ys)", "(ys ++ xs)"
--
getDiff : Term → Term → (Term × Term × Term)
getDiff (var x args) t2 = {!!}
getDiff (con c args) t2 = {!!}
getDiff (def f args) t2 = {!!}
getDiff (lam v t1) t2 = {!!}
getDiff (pat-lam cs args) t2 = {!!}
getDiff (pi t₁ t₂) t2 = {!!}
getDiff (sort x) t2 = {!!}
getDiff (lit x) t2 = {!!}
getDiff unknown t2 = {!!}
