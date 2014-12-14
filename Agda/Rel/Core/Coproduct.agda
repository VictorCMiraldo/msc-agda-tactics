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
record either {A B C : Set}(R : Rel A C)(S : Rel B C)(c : C)(ab : A ⊎ B) : Set
  where constructor cons-either
        field un : case (R c) (S c) ab

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
coprod-uni-r1 {X = X} r s (prf1 , prf2)
  = ⊆in (λ a c hip → i1 a , (⊆out prf2) (i1 a) c (cons-either hip) , cons-fun refl) 
  , ⊆in (λ a c hip → let wit , hprf = hip
                     in either.un
                          (⊆out prf1 (i1 a) c
                           (subst (X c) (sym (fun.un (p2 hprf))) (p1 hprf))))

coprod-uni-r2 : ∀{A B C}{X : Rel (A ⊎ B) C}
              → (R : Rel A C) → (S : Rel B C)
              → (X ≡r either R S) 
              → S ≡r X ∙ ι₂
coprod-uni-r2 {X = X} r s (prf1 , prf2)
  = ⊆in (λ b c hip → i2 b , (⊆out prf2) (i2 b) c (cons-either hip) , cons-fun refl)
  , ⊆in (λ b c hip → let wit , hprf = hip 
                     in either.un ((⊆out prf1) (i2 b) c (subst (X c) (sym (fun.un (p2 hprf))) (p1 hprf))))

-- The left proof will be provided by two auxiliary proofs, since it is a big one.
--
-- Left implication
--
coprod-uni-l-aux1 : ∀{A B C}{X : Rel (A ⊎ B) C}
                  → (R : Rel A C) → (S : Rel B C)
                  → (R ≡r X ∙ ι₁) → (S ≡r X ∙ ι₂)
                  → X ⊆ either R S
coprod-uni-l-aux1  {X = X} r s pr ps
  = ⊆in λ { (i1 a) c hip → cons-either ((⊆out (≡r-elim2 pr)) a c (coprod-lemma-i1 {X = X} a c hip))
          ; (i2 b) c hip → cons-either ((⊆out (≡r-elim2 ps)) b c (coprod-lemma-i2 {X = X} b c hip))
          }
  where
    coprod-lemma-i1 : ∀{A B C}{X : Rel (A ⊎ B) C}
                    → (a : A) → (c : C)
                    → X c (i1 a) 
                    → (X ∙ ι₁) c a
    coprod-lemma-i1 a c cXi1a = i1 a , cXi1a , cons-fun refl 

    coprod-lemma-i2 : ∀{A B C}{X : Rel (A ⊎ B) C}
                    → (b : B) → (c : C)
                    → X c (i2 b) 
                    → (X ∙ ι₂) c b
    coprod-lemma-i2 b c cXi2b = i2 b , cXi2b , cons-fun refl


-- Right implication
--
coprod-uni-l-aux2 : ∀{A B C}{X : Rel (A ⊎ B) C}
                  → (R : Rel A C) → (S : Rel B C)
                  → (R ≡r X ∙ ι₁) → (S ≡r X ∙ ι₂)
                  → either R S ⊆ X
coprod-uni-l-aux2 {X = X} r s pr ps
  = ⊆in λ { (i1 a) c hip → let a1 , a2 = (⊆out (≡r-elim1 pr)) a c (either.un hip)
                           in subst (X c) (sym (fun.un (p2 a2))) (p1 a2)
          ; (i2 b) c hip → let a1 , a2 = (⊆out (≡r-elim1 ps)) b c (either.un hip)
                           in subst (X c) (sym (fun.un (p2 a2))) (p1 a2)
          }

-- And, finally, the universal.
coprod-uni-l : ∀{A B C}{X : Rel (A ⊎ B) C}
             → (R : Rel A C) → (S : Rel B C)
             → (R ≡r X ∙ ι₁) → (S ≡r X ∙ ι₂)
             → X ≡r either R S
coprod-uni-l r s pr ps = ≡r-intro (coprod-uni-l-aux1 r s pr ps) (coprod-uni-l-aux2 r s pr ps)

