open import Rel.Core
open import Rel.Core.Equality

module Rel.Properties.Neutral where

  -- Id is left neutral
  ∙-id-l : ∀{A B}{R : Rel A B}
         → R ≡r Id ∙ R
  ∙-id-l {R = R}
         = ⊆in (λ a b bRa → b , cons-fun refl , bRa) 
         , ⊆in (λ a b bIdRa → subst (λ x → R x a) (fun.un $ p1 (p2∙ bIdRa)) (p2 (p2∙ bIdRa)) )

  -- Id is right neutral
  ∙-id-r : ∀{A B}(R : Rel A B)
         → R ≡r R ∙ Id
  ∙-id-r R = ⊆in (λ a b bRa → a , bRa , cons-fun refl)
           , ⊆in (λ a b bRIda → subst (R b) (sym (fun.un $ p2 (p2∙ bRIda))) (p1 (p2∙ bRIda)) )
