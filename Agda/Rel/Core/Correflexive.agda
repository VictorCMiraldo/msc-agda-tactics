module Rel.Core.Correflexive where

open import Relation.Binary.PropositionalEquality
open import Data.Product using (_×_)
open import Rel.Core.Core using (Rel)

-----------------------
-- * Correflexives * --
-----------------------

record φ {A : Set}(P : A → Set)(a₁ : A)(a₂ : A) : Set
  where constructor cons-φ
        field un : a₁ ≡ a₂ × P a₁
