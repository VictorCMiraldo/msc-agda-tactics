module Rel.Core.Correflexive where

open import Relation.Binary.PropositionalEquality
open import Data.Product using (_×_)
open import Rel.Core.Core using (Rel)

-----------------------
-- * Correflexives * --
-----------------------

φ : {A : Set}(P : A → Set) → Rel A A
φ p = λ a a′ → a ≡ a′ × p a 
