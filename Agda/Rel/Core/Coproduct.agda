module Rel.Core.Coproduct where

open import Data.Bool using (Bool; true; false)
open import Relation.Binary.PropositionalEquality
open import Data.Product using (_×_; ∃; _,_) renaming (proj₁ to p1; proj₂ to p2)
open import Data.Sum using (_⊎_; [_,_]) renaming (inj₁ to i1; inj₂ to i2; [_,_]′ to case)
open import Function using (id; _∘_)

open import Data.Unit using (Unit)
open import Data.Empty using (⊥)

open import Rel.Core.Core
open import Rel.Core.Equality

----------------------
-- ** Coproducts ** --
----------------------

-- Either
either : {A B C : Set} → (R : Rel A C) → (S : Rel B C) → Rel (A ⊎ B) C
either R S c ab = case (R c) (S c) ab

-- Coproduct constants
ι₁ : {A B : Set} → Rel A (A ⊎ B)
ι₁ = fun i1

ι₂ : {A B : Set} → Rel B (A ⊎ B)
ι₂ = fun i2

-- Sum
_+_ : {A B C D : Set} → (R : Rel A B) → (S : Rel C D) → Rel (A ⊎ C) (B ⊎ D)
R + S = either (ι₁ ∙ R) (ι₂ ∙ S)

------------------
-- Coproduct Universal

coprod-uni-r1 : ∀{A B C}{X : Rel (A ⊎ B) C}
              → (R : Rel A C) → (S : Rel B C)
              → (X ≡r either R S) 
              → R ≡r X ∙ ι₁
coprod-uni-r1 {X = X} r s prf
  = (λ c a hip → i1 a , ≡r-elim2 prf c (i1 a) hip , refl) 
  , (λ c a hip → let wit , hprf = hip
                 in ≡r-elim1 prf c (i1 a) (subst (X c) (sym (p2 hprf)) (p1 hprf)))

coprod-uni-r2 : ∀{A B C}{X : Rel (A ⊎ B) C}
              → (R : Rel A C) → (S : Rel B C)
              → (X ≡r either R S) 
              → S ≡r X ∙ ι₂
coprod-uni-r2 {X = X} r s prf
  = (λ c b hip → i2 b , ≡r-elim2 prf c (i2 b) hip , refl)
  , (λ c b hip → let wit , hprf = hip 
                 in ≡r-elim1 prf c (i2 b) (subst (X c) (sym (p2 hprf)) (p1 hprf)))

-- The left proof will be provided by two auxiliary proofs, since it is a big one.
--
-- Left implication
--
coprod-uni-l-aux1 : ∀{A B C}{X : Rel (A ⊎ B) C}
                  → (R : Rel A C) → (S : Rel B C)
                  → (R ≡r X ∙ ι₁) → (S ≡r X ∙ ι₂)
                  → X ⊆ either R S
coprod-uni-l-aux1  {X = X} r s pr ps
  = λ { c (i1 a) hip → (≡r-elim2 pr) c a (coprod-lemma-i1 {X = X} a c hip)
      ; c (i2 b) hip → (≡r-elim2 ps) c b (coprod-lemma-i2 {X = X} b c hip)
      }
  where
    coprod-lemma-i1 : ∀{A B C}{X : Rel (A ⊎ B) C}
                    → (a : A) → (c : C)
                    → X c (i1 a) 
                    → (X ∙ ι₁) c a
    coprod-lemma-i1 a c cXi1a = i1 a , cXi1a , refl 

    coprod-lemma-i2 : ∀{A B C}{X : Rel (A ⊎ B) C}
                    → (b : B) → (c : C)
                    → X c (i2 b) 
                    → (X ∙ ι₂) c b
    coprod-lemma-i2 b c cXi2b = i2 b , cXi2b , refl

-- Right implication
--
coprod-uni-l-aux2 : ∀{A B C}{X : Rel (A ⊎ B) C}
                  → (R : Rel A C) → (S : Rel B C)
                  → (R ≡r X ∙ ι₁) → (S ≡r X ∙ ι₂)
                  → either R S ⊆ X
coprod-uni-l-aux2 {X = X} r s pr ps
  = λ { c (i1 a) hip → let aux = ≡r-elim1 pr c a hip
                       in subst (X c) (sym (p2 (p2 aux))) (p1 (p2 aux))
      ; c (i2 b) hip → let aux = ≡r-elim1 ps c b hip
                       in subst (X c) (sym (p2 (p2 aux))) (p1 (p2 aux))
      }

-- And, finally, the universal.
coprod-uni-l : ∀{A B C}{X : Rel (A ⊎ B) C}
             → (R : Rel A C) → (S : Rel B C)
             → (R ≡r X ∙ ι₁) → (S ≡r X ∙ ι₂)
             → X ≡r either R S
coprod-uni-l r s pr ps = ≡r-intro (coprod-uni-l-aux1 r s pr ps) (coprod-uni-l-aux2 r s pr ps)
