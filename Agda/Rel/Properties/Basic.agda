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

  -- Provides an easy way to 'pull' something to a parenthesis.
  ∙-assoc-join : ∀{A B C D E}{R : Rel A B}{S : Rel B C}{T : Rel C D}{U : Rel D E}
               → (U ∙ T) ∙ S ∙ R ≡r (U ∙ T ∙ S) ∙ R
  ∙-assoc-join {R = R} {S = S} {T = T} {U = U}
    = ≡r-trans (≡r-sym (∙-assoc {R = R} {S = S} {T = U ∙ T})) 
               (≡r-cong (λ i → i ∙ R) ∙-assoc)

  ᵒ-idp : {A B : Set}{R : Rel A B} → (R ᵒ) ᵒ ≡r R
  ᵒ-idp = (⊆in (λ a b z → z)) , (⊆in (λ a b z → z))

  ᵒ-∙-distr : {A B C : Set}{R : Rel A B}{S : Rel B C}
            → R ᵒ ∙ S ᵒ ≡r (S ∙ R) ᵒ
  ᵒ-∙-distr = (⊆in (λ a b x → p1∙ x , (p2 $ p2∙ x) , (p1 $ p2∙ x))) 
            , (⊆in (λ a b x → p1∙ x , (p2 $ p2∙ x) , (p1 $ p2∙ x)))

  ᵒ-∙-distr3 : {A B C D : Set}{R : Rel A B}{S : Rel B C}{T : Rel C D}
             → R ᵒ ∙ S ᵒ ∙ T ᵒ ≡r (T ∙ S ∙ R) ᵒ
  ᵒ-∙-distr3 {R = R} {S = S} {T = T}
    = ≡r-trans ᵒ-∙-distr 
         (≡r-trans (≡r-cong (λ i → (i ∙ R) ᵒ) (≡r-sym ᵒ-∙-distr)) 
            (≡r-trans (≡r-cong (λ i → ((i ∙ (S ᵒ) ᵒ) ∙ R) ᵒ) ᵒ-idp) 
              (≡r-trans (≡r-cong (λ i → ((T ∙ i) ∙ R) ᵒ) ᵒ-idp) 
                (≡r-cong (λ i → i ᵒ) ∙-assoc))))

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
