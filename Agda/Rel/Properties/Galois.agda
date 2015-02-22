open import Rel.Core
open import Rel.Core.Equality

module Rel.Properties.Galois where

  record _⊢_ {A B C D : Set}
              (lw : Rel A B → Rel C D)
              (up : Rel C D → Rel A B) : Set1
    where
      field 
        cancel-lw : ∀{R} → lw (up R) ⊆ R
        cancel-up : ∀{R} → R ⊆ up (lw R)

        distr-lw : ∀{R S} → lw R ∪ lw S ≡r lw (R ∪ S)
        distr-up : ∀{R S} → up R ∩ up S ≡r up (R ∩ S)
  

  instance
    ᵒ-isGC : {A B : Set} → IsGC {A} {B} {B} {A} (_ᵒ) (_ᵒ)
    ᵒ-isGC = record
      { cancel-lw = {!!}
      ; cancel-up = {!!}
      ; distr-lw  = {!!}
      ; distr-up  = {!!}
      }
        
         
