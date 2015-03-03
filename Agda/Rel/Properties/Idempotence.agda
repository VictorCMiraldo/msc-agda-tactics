open import Rel.Core
open import Rel.Core.Equality

module Rel.Properties.Idempotence where

  idmp-id-ᵒ : {A : Set} → Id {A} ≡r Id ᵒ
  idmp-id-ᵒ = ⊆in (λ a b i → cons-fun (sym (fun.un i))) 
            , ⊆in (λ a b i → cons-fun (sym (fun.un i)))
