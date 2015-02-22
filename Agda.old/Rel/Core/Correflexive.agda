module Rel.Core.Correflexive where

open import Relation.Binary.PropositionalEquality
open import Data.Product using (_×_; _,_)
open import Rel.Core.Core
open import Rel.Core.HOTT using (isProp)

-----------------------
-- * Correflexives * --
-----------------------

record φ {A : Set}(P : A → Set)(a₁ : A)(a₂ : A) : Set
  where constructor cons-φ
        field un : a₁ ≡ a₂ × P a₁

record IsPredicate {A : Set}(P : A → Set) : Set
  where constructor pred
        field prf : ∀ a → isProp (P a)

instance 
  φ-isProp : {A : Set}{P : A → Set}{{ r : IsPredicate P }} → IsProp (φ P)
  φ-isProp ⦃ pred prf ⦄ = Rel.Core.Core.mp 
    (λ { b a (cons-φ p₁) (cons-φ p₂) → cong cons-φ (same a b p₁ p₂ (prf a)) })
    where
      same : {A : Set}{P : A → Set}(a b : A)(p1 : b ≡ a × P b)(p2 : b ≡ a × P b)
           → isProp (P a) → p1 ≡ p2
      same a .a (refl , p12) (refl , p22) prfa with prfa p12 p22
      same a .a (refl , p12) (refl , .p12) prfa | refl = refl
