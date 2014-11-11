module Rel.CaseStudies.Simple1 where

open import Data.Bool using (Bool; true; false)
open import Relation.Binary.PropositionalEquality
open import Data.Product using (_×_; ∃; _,_) renaming (proj₁ to p1; proj₂ to p2)
open import Data.Sum using (_⊎_; [_,_]) renaming (inj₁ to i1; inj₂ to i2; [_,_]′ to case)
open import Function using (id; _∘_)

open import Data.Unit using (Unit; unit)
open import Data.Empty using (⊥; ⊥-elim)

open import Data.Nat using (ℕ; zero; suc)

open import Rel.Core.Core
open import Rel.Core.Correflexive
open import Rel.Core.Equality
open import Rel.Reasoning.SubsetJudgement
open import Rel.Properties

twice : ℕ → ℕ
twice zero    = zero
twice (suc n) = suc (suc (twice n))

twiceR : Rel ℕ ℕ
twiceR = fun twice

even : ℕ → Bool
even zero          = true
even (suc zero)    = false
even (suc (suc n)) = even n

So : Bool → Set
So true  = Unit
So false = ⊥

evenR : Rel ℕ ℕ
evenR = φ (So ∘ even)

twiceIsEven : (twiceR ⊆ twiceR) ⇐ (twiceR ⊆ twiceR ∙ Id)
twiceIsEven 
  = begin
    twiceR ⊆ twiceR
  ≡⟨ subst-r (∙-id-r twiceR) ⟩
    twiceR ⊆ twiceR ∙ Id
  ∎

twiceInTwice : Unit ⇐ (twiceR ⊆ twiceR) 
twiceInTwice 
  = {! lemma (∙-id-r twiceR)!}

{-
≡r-equivalence : {A B : Set} → IsEquivalence (_≡r_ {A = A} {B = B})
≡r-equivalence = record
  { refl  = ≡r-refl
  ; sym   = ≡r-sym
  ; trans = ≡r-trans
  }

⊆-IsPreorder : {A B : Set} → IsPreorder (_≡r_ {A = A} {B = B}) _⊆_
⊆-IsPreorder = record
  { isEquivalence = ≡r-equivalence
  ; reflexive     = p1
  ; trans         = ⊆-trans
  }

⊆-Preorder : {A B : Set} → Preorder (Level.suc Level.zero) Level.zero Level.zero
⊆-Preorder {A} {B} = record
  { Carrier = Rel.Core.Rel A B
  ; _≈_     = _≡r_
  ; _∼_     = _⊆_
  ; isPreorder = ⊆-IsPreorder
  }

import Relation.Binary.PreorderReasoning as Pre

twiceIsEven : twiceR ∙ evenR ⊆ evenR ∙ twiceR
twiceIsEven 
  = begin
    twiceR ∙ evenR  -- twiceR ∙ evenR ⊆ evenR ∙ twiceR
  ∼⟨ ∙-subst-r (ρ-intro evenR) ⟩
    twiceR ∙ (ρ evenR ∙ evenR)
  ∼⟨ {!!} ⟩
    {!!}
  ∎
  where open Pre ⊆-Preorder
-}

