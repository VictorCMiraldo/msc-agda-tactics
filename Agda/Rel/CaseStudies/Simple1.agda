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

-- TODO: solve this two problems!
evenLemma : evenR ≡ ρ twiceR
evenLemma = {!!}

≡r-promote : {A B : Set}{R S : Rel A B}
           → R ≡r S → R ≡ S
≡r-promote (r⊆s , s⊆r) = {!!}

twiceIsEven : (twiceR ∙ evenR ⊆ evenR ∙ twiceR) ⇐ Unit
twiceIsEven 
  = begin

    twiceR ∙ evenR ⊆ evenR ∙ twiceR

  ⇐⟨ subst (λ x → twiceR ∙ evenR ⊆ x ∙ twiceR) (sym evenLemma) ⟩

    twiceR ∙ evenR ⊆ ρ twiceR ∙ twiceR

  ⇐⟨ subst (λ x → twiceR ∙ evenR ⊆ x) (≡r-promote (ρ-intro twiceR)) ⟩

    twiceR ∙ evenR ⊆ twiceR

  ⇐⟨ subst (λ x → twiceR ∙ evenR ⊆ x) (≡r-promote (≡r-sym (∙-id-r twiceR))) ⟩

    twiceR ∙ evenR ⊆ twiceR ∙ Id

  ⇐⟨ ∙-monotony ⟩

    (twiceR ⊆ twiceR × evenR ⊆ Id)

  ⇐⟨ (λ _ → ⊆-refl , φ⊆Id) ⟩

    Unit

  ∎
