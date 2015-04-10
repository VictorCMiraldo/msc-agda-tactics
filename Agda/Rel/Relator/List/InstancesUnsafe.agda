open import Prelude hiding (_*_; _+_; _++_) renaming (either to +-elim)

open import Rel.Core
open import Rel.Core.Equality
open import Rel.Core.Product
open import Rel.Core.Coproduct
open import Rel.Relator
open import Rel.Relator.List

-- See Rel.Relator.List.Instances

module Rel.Relator.List.InstancesUnsafe where

  open IsWFunctor1 {{...}}

  instance
    postulate
      isDec-L : {X Y A : Set}{R : Rel X Y}{{ dR : IsDec R }}{{ eqA : Eq A }}
              → IsDec (Fᵣ {F = L} {X = A} R)
   
      isDec-cataL : {A B : Set}{R : Rel (L A B) B}{{ dR : IsDec R }}{{ c : Composes (R ∙ ι₂) (Id * ⟦ R ⟧₁) }}
                  → IsDec ⟦ R ⟧₁
   
