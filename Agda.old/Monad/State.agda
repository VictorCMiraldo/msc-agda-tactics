module Monad.State where

{-

Somewhat simpler State Monad from the one provided
by the Agda standard library.

-}

open import Data.Unit
open import Data.Product using (_×_; _,_) renaming (proj₁ to p1; proj₂ to p2)
open import Function using (_∘_)

-----------------------------------------------------------
-- * State Monadic wrapper

record ST (s : Set)(a : Set) : Set1 where
  field
    unST : s → (a × s)

runST : ∀{a s} → ST s a → s → (a × s)
runST r = (ST.unST r)

evalST : ∀{a s} → ST s a → s → a
evalST r = p1 ∘ (runST r)

return : ∀{a s} → a → ST s a
return x = record { unST = λ s → (x , s) }

infixr 8 _>>=_
_>>=_ : ∀{a b s} → ST s a → (a → ST s b) → ST s b
x >>= f = record { unST = λ s →
                              let x′ : _
                                  x′ = runST x s
                              in  runST (f (p1 x′)) (p2 x′)
                 }

infixr 8 _>>_
_>>_ : ∀{a b s} → ST s a → ST s b → ST s b
x >> f = x >>= λ _ → f

get : ∀{s} → ST s s
get = record { unST = λ s → (s , s) }

put : ∀{s} → s → ST s Unit
put x = record { unST = λ _ → (unit , x) }
 
modify : ∀{s} → (s → s) → ST s Unit
modify f = record { unST = λ s → (unit , f s) }

--------------------------------------------------------------
-- * Applicative Style Interface

infix 11 _<$>_
_<$>_ : ∀{s}{a b : Set} → (a → b) → ST s a → ST s b
f <$> s = s >>= return ∘ f

infixl 10 _<*>_
_<*>_ : ∀{s}{a b : Set} → ST s (a → b) → ST s a → ST s b
f <*> s = f >>= \f′ → s >>= return ∘ f′

