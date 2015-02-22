open import Rel.Core
open import Rel.Core.Equality

-- Operators _∩_, _∪_, _∙_ and _ᵒ are monotonous with respect
-- to ⊆.
module Rel.Properties.Monotonicity where

  ∙-mono : {A B C : Set}{S T : Rel B C}{Q R : Rel A B}
         → S ⊆ T → Q ⊆ R → S ∙ Q ⊆ T ∙ R
  ∙-mono (⊆in st) (⊆in qr) 
    = ⊆in (λ a c bSQa
          → let b   = p1∙ bSQa
                cSb = p1 (p2∙ bSQa)
                bQa = p2 (p2∙ bSQa)
            in b , st b c cSb , qr a b bQa)

  ∩-mono : {A B : Set}{R S Q T : Rel A B}
         → S ⊆ T → Q ⊆ R → S ∩ Q ⊆ T ∩ R
  ∩-mono (⊆in st) (⊆in qr) 
    = ⊆in (λ a b bSQa → cons-∩ (st a b (p1∩ bSQa) , qr a b (p2∩ bSQa)))

  ∪-mono : {A B : Set}{R S Q T : Rel A B}
         → S ⊆ T → Q ⊆ R → S ∪ Q ⊆ T ∪ R
  ∪-mono (⊆in st) (⊆in qr)  
    = ⊆in (λ { a b (cons-∪ (i1 bSa)) → cons-∪ (i1 (st a b bSa))
             ; a b (cons-∪ (i2 bQa)) → cons-∪ (i2 (qr a b bQa))
             })

  ᵒ-mono : {A B : Set}{R S : Rel A B}
         → R ⊆ S → R ᵒ ⊆ S ᵒ
  ᵒ-mono (⊆in rs) = ⊆in (λ a b → rs b a)
