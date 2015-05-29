open import Prelude hiding (_+_; _*_) renaming (either to +-elim)

open import RW.Language.RTerm

open import Rel.Core
open import Rel.Core.Equality
open import Rel.Core.Product
open import Rel.Core.Coproduct
open import Rel.Properties.Basic
open import Rel.Properties.BiFunctor
open import Rel.Properties.Idempotence
open import Rel.Properties.Correflexive

module Rel.Properties.DatabaseList where

  db : List Name
  db = (quote ∪-uni-l)
     ∷ (quote ∪-uni-r)
     ∷ (quote ∩-uni-l)
     ∷ (quote ∩-uni-r)
     ∷ (quote prod-uni-r1)
     ∷ (quote prod-uni-r2)
     ∷ (quote prod-uni-l)
     ∷ (quote coprod-uni-r1)
     ∷ (quote coprod-uni-r2)
     ∷ (quote coprod-uni-l)
     ∷ (quote ∙-assoc)
     ∷ (quote ∙-assoc-join)
     ∷ (quote ᵒ-idp)
     ∷ (quote ᵒ-∙-distr)
     ∷ (quote ∙-id-l)
     ∷ (quote ∙-id-r)
     ∷ (quote π₁-natural)
     ∷ (quote π₂-natural)
     ∷ (quote *-bi-functor)
     ∷ (quote *-ᵒ-distr)
     ∷ (quote *-id)
     ∷ (quote ι₁-natural)
     ∷ (quote ι₁-cancel)
     ∷ (quote ι₂-natural)
     ∷ (quote ι₂-cancel)
     ∷ (quote +-bi-functor)
     ∷ (quote +-ᵒ-distr)
     ∷ (quote +-id)
     ∷ (quote either-+-abs)
     ∷ (quote either-abs)
     ∷ (quote φ≡φᵒ)
     ∷ (quote φ≡φ∙φ)
     ∷ (quote φ⊆Id)
     ∷ (quote ρ-intro)
     ∷ []
