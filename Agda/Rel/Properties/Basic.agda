open import Rel.Core
open import Rel.Core.Equality

module Rel.Properties.Basic where

  R⊆Top : ∀{A B : Set}{R : Rel A B}
        → R ⊆ Top
  R⊆Top = ⊆in (λ _ _ _ → unit) 

  Bot⊆R : ∀{A B : Set}{R : Rel A B}
        → Bot ⊆ R
  Bot⊆R = ⊆in (λ _ _ → λ ())

  -- Relational composition is left associative
  ∙-assocl : ∀{A B C D}{R : Rel A B}{S : Rel B C}{T : Rel C D}
           → T ∙ (S ∙ R) ⊆ (T ∙ S) ∙ R
  ∙-assocl = ⊆in (λ a d hip 
    → let (c , dTc , b , cSb , bRa) = hip
      in b , (c , dTc , cSb) , bRa)

  -- And right associative
  ∙-assocr : ∀{A B C D}{R : Rel A B}{S : Rel B C}{T : Rel C D}
           → (T ∙ S) ∙ R ⊆ T ∙ (S ∙ R)
  ∙-assocr = ⊆in (λ a d hip
    → let (b , (c , dTc , cSb) , bRa) = hip
      in c , dTc , b , cSb , bRa)

  -- Wrapper for associativity
  ∙-assoc : ∀{A B C D}{R : Rel A B}{S : Rel B C}{T : Rel C D}
          → (T ∙ S) ∙ R ≡r T ∙ (S ∙ R)
  ∙-assoc = ≡r-intro ∙-assocr ∙-assocl

  -- Id is left neutral
  ∙-id-l : ∀{A B}{R : Rel A B}
         → R ≡r Id ∙ R
  ∙-id-l {R = R}
         = ⊆in (λ a b bRa → b , cons-fun refl , bRa) 
         , ⊆in (λ a b bIdRa → subst (λ x → R x a) 
                  (fun.un (p1 (p2∙ bIdRa))) (p2 (p2∙ bIdRa)) )

  -- Id is right neutral
  ∙-id-r : ∀{A B}(R : Rel A B)
         → R ≡r R ∙ Id
  ∙-id-r R = ⊆in (λ a b bRa → a , bRa , cons-fun refl)
           , ⊆in (λ a b bRIda → subst (R b) 
                    (sym (fun.un (p2 (p2∙ bRIda)))) (p1 (p2∙ bRIda)) )
