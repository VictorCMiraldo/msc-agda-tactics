open import Rel.Core
open import Rel.Core.Equality
open import Rel.Core.Shrinking

module Rel.Properties.Galois where

  -- A Galois Connection is the algebrist best friend. Loads of
  -- properties from Relational Algebra arise as Galois Connection
  -- corolaries.
  --
  -- Although formally one only needs to prove the connection:
  --
  --   φ R ⊆ S ≡ R ⊆ ψ S
  --
  -- and the properties comes for free, in Agda it 
  -- doesn't quite work like that... Therefore
  -- the user should prove a few more properties.
  --
  record _⊢_ {A B C D : Set}
             (φ : Rel A B → Rel C D)
             (ψ : Rel C D → Rel A B) 
             : Set1 where 
    field
      gc-1 : {R : Rel A B}{S : Rel C D}
           → φ R ⊆ S → R ⊆ ψ S

      gc-2 : {R : Rel A B}{S : Rel C D}
           → R ⊆ ψ S → φ R ⊆ S

      gc-distr-1 : {R S : Rel A B}
                 → φ (R ∪ S) ≡r φ R ∪ φ S

      gc-distr-2 : {R S : Rel C D}
                 → ψ (R ∩ S) ≡r ψ R ∩ ψ S

      gc-mono-1 : {R S : Rel A B}
                → R ⊆ S → φ R ⊆ φ S

      gc-mono-2 : {R S : Rel C D}
                → R ⊆ S → ψ R ⊆ ψ S

    gc-cancel-1 : {R : Rel A B}
                → R ⊆ ψ (φ R)
    gc-cancel-1 = gc-1 ⊆-refl

    gc-cancel-2 : {S : Rel C D}
                → φ (ψ S) ⊆ S
    gc-cancel-2 = gc-2 ⊆-refl        
  

  instance
    ᵒ-isGC : {A B : Set} → _⊢_ {A} {B} {B} {A} (_ᵒ) (_ᵒ)
    ᵒ-isGC = record
      { gc-1 = λ { (⊆in prf) → ⊆in (λ a b → prf b a) }
      ; gc-2 = λ { (⊆in prf) → ⊆in (λ a b → prf b a) }
      ; gc-distr-1 = ⊆in (λ a b z → cons-∪ (_∪_.un z))
                   , ⊆in (λ a b z → cons-∪ (_∪_.un z))
      ; gc-distr-2 = ⊆in (λ a b z → cons-∩ (_∩_.un z))
                   , ⊆in (λ a b z → cons-∩ (_∩_.un z))
      ; gc-mono-1 = λ { (⊆in prf) → ⊆in (λ a b → prf b a) }
      ; gc-mono-2 = λ { (⊆in prf) → ⊆in (λ a b → prf b a) }
      }
        
    ∙-/-isGC : {A B C : Set}{Y : Rel B A} 
             → _⊢_ {A} {C} {B} {C} (λ R → R ∙ Y) (λ S → S / Y)
    ∙-/-isGC = record
      { gc-1 = λ { (⊆in prf) 
                 → ⊆in (λ a b z → cons-/ (λ b₁ z₁ → prf b₁ b (a , (z , z₁)))) 
                 }
      ; gc-2 = λ { (⊆in prf) 
                 → ⊆in (λ b c z 
                 → let cSYz = prf (p1∙ z) c (p1 (p2∙ z))
                   in _/_.un cSYz b (p2 (p2∙ z)))
                 }
      ; gc-distr-1 
        = ⊆in (λ b c z 
          → cons-∪ (case (λ r → i1 (p1∙ z , r , p2 (p2∙ z))) 
                         (λ r → i2 (p1∙ z , r , p2 (p2∙ z))) 
                         (_∪_.un (p1 (p2∙ z)))) 
                   )
        , ⊆in (λ { b c (cons-∪ (i1 x)) 
                   → p1∙ x , cons-∪ (i1 (p1 (p2∙ x))) , p2 (p2∙ x) 
                 ; b c (cons-∪ (i2 y)) 
                   → p1∙ y , cons-∪ (i2 (p1 (p2∙ y))) , p2 (p2∙ y)
                 })
      ; gc-distr-2 
        = ⊆in (λ { a c (cons-/ h) 
          → cons-∩ (cons-/ (λ b → p1∩ ∘ h b) , cons-/ (λ b → p2∩ ∘ h b)) }) 
        , ⊆in (λ { a c (cons-∩ (cons-/ h1 , cons-/ h2))
          → cons-/ (λ b z → cons-∩ (h1 b z , h2 b z)) })
      ; gc-mono-1 
        = λ { (⊆in rs) 
          → ⊆in (λ b c z 
            → p1∙ z , rs (p1∙ z) c (p1 (p2∙ z)) , p2 (p2∙ z)) }
      ; gc-mono-2 
        = λ { (⊆in rs) 
          → ⊆in (λ { a c (cons-/ bRYa) 
            → cons-/ (λ b → rs b c ∘ bRYa b) }) }
      }

    ∙-\\-isGC : {A B : Set}{Y : Rel A B} 
              → _⊢_ {A} {A} {A} {B} (λ R → Y ∙ R) (λ S → Y \\ S)
    ∙-\\-isGC = record
      { gc-1 = λ { (⊆in hip) 
                 → ⊆in (λ a₁ a₂ a₂Ra₁ → cons-\ (λ b bYa₁ → hip a₂ b ({!!} , {!!} , {!!}))) 
                 }
      ; gc-2 = λ { {R = R} (⊆in hip)
                 → ⊆in (λ a b bYRa → _\\_.un (hip (p1∙ bYRa) a {!!}) b {!!}) 
                 }
      ; gc-distr-1 = {!!}
      ; gc-distr-2 = {!!}
      ; gc-mono-1  = {!!}
      ; gc-mono-2  = {!!}
      }

    δ-Top-isGC : {A B : Set}
               → _⊢_ {A} {B} δ (_∙_ Top)
    δ-Top-isGC = TODO
      where postulate TODO : ∀{a}{A : Set a} → A

    ρ-Top-isGC : {A B : Set}
               → _⊢_ {A} {B} ρ (λ R → R ∙ Top)
    ρ-Top-isGC = TODO
      where postulate TODO : ∀{a}{A : Set a} → A
