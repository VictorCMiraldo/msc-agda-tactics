open import Data.Bool using (Bool; true; false)
open import Relation.Binary.PropositionalEquality as PE
open import Data.Product using (Σ; _×_; ∃; _,_; uncurry′; curry) renaming (proj₁ to p1; proj₂ to p2)
open import Data.Sum using (_⊎_; [_,_]) renaming (inj₁ to i1; inj₂ to i2; [_,_]′ to case)
open import Function using (id; _∘_)

open import Rel.Core.Core

module Rel.Core.Shrinking where

  -- Relational Division
  record _/_ {A B C : Set}(R : Rel B C)(S : Rel B A)(c : C)(a : A) : Set
    where 
      constructor cons-/
      field un : (b : B) → S a b → R c b

  -- Shrinking. Emacs input is \u0
  record _↾_ {A B : Set}(R : Rel A B)(S : Rel B B)(b : B)(a : A) : Set
    where
      constructor cons-↾
      field un : (R ∩ (S / (R ᵒ))) b a

  shrink-uni-l1 : {A B : Set}(X R : Rel A B)(S : Rel B B)
                → X ⊆ (R ↾ S)
                → X ⊆ R
  shrink-uni-l1 x r s (⊆in prf) 
    = ⊆in (λ a b bXa → let bRSa = prf a b bXa
                       in p1∩ (_↾_.un bRSa))

  shrink-uni-l2 : {A B : Set}(X R : Rel A B)(S : Rel B B)
                → X ⊆ (R ↾ S)
                → (X ∙ R ᵒ) ⊆ S
  shrink-uni-l2 x r s (⊆in prf) 
    = ⊆in (λ { b b′ (a , ∙prf) 
           → let bRSa = prf a b′ (p1 ∙prf)
                 bRx→bSx = _/_.un (p2∩ (_↾_.un bRSa))
             in bRx→bSx b (p2 ∙prf) })

  shrink-uni-r : {A B : Set}(X R : Rel A B)(S : Rel B B)
               → X ⊆ R → (X ∙ R ᵒ) ⊆ S
               → X ⊆ (R ↾ S)
  shrink-uni-r x r s (⊆in xr) (⊆in xrs)
    = ⊆in (λ a b bXa 
           → let bRa = xr a b bXa
                 bXRb₁ = λ b₁ bR∘a → a , bXa , bR∘a
             in cons-↾ (cons-∩ ( bRa 
                               , cons-/ (λ b₁ bR∘a → xrs b₁ b (bXRb₁ b₁ bR∘a)))
                               )
                       )
