module Rewr where

open import Data.Bool
open import Data.Nat as N using (ℕ; zero; suc; _+_) renaming (_≟_ to _≟-Nat_)
open import Data.String using (String)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_) renaming (proj₁ to p1; proj₂ to p2)
open import Data.List using (List; []; _∷_; _++_; map; length)
open import Relation.Nullary.Decidable as Dec
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Reflection
open import Relation.Nullary using (Dec; yes; no)
open import Function using (_∘_)
open import Data.Unit using (Unit; unit)
open import Data.Empty using (⊥; ⊥-elim)

open import Rel.Core.Core renaming (Rel to R)
open import Rel.Core.Equality
open import Rel.Reasoning.SubsetJudgement
open import Rel.Properties

---------------------------------------------------------
-- Test

open import Level using (Level)

goalTest1 : {A B : Set}(R : R A B) → (R ⊆ R ∙ Id) ⇐ Unit
goalTest1 R 
  = begin
    R ⊆ R ∙ Id
  ⇐⟨ (quoteGoal g in {!quoteTerm (R ∙ Id) !}) ⟩
    R ⊆ R
  ⇐⟨ (λ _ → ⊆-refl) ⟩
    Unit
  ∎
