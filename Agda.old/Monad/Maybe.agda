module Monad.Maybe where

open import Data.Maybe using (Maybe; just; nothing)

return : ∀{a}{A : Set a} → A → Maybe A
return = just

_>>=_ : ∀{a b}{A : Set a}{B : Set b} → Maybe A → (A → Maybe B) → Maybe B
nothing >>= _ = nothing
just x  >>= f = f x

_>>_ : ∀{a b}{A : Set a}{B : Set b} → Maybe A → Maybe B → Maybe B
f >> g = g >>= λ _ → g
