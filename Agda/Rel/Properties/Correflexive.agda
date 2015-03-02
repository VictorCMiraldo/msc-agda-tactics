open import Rel.Core
open import Rel.Core.Equality
open import Rel.Core.Correflexive

module Rel.Properties.Correflexive where

  φ≡φᵒ : {A : Set}{P : A → Set}
       → φ P ≡r (φ P) ᵒ
  φ≡φᵒ {A} {P} = ⊆in aux1 , ⊆in aux2
    where
      aux1 : (a b : A) → φ P b a → (φ P ᵒ) b a
      aux1 a b (cons-φ (prf , pa)) 
        rewrite prf = cons-φ (refl , pa)

      aux2 : (a b : A) → (φ P ᵒ) b a → φ P b a
      aux2 a b (cons-φ (prf , pa)) 
        rewrite prf = cons-φ (refl , pa)

  φ≡φ∙φ : {A : Set}{P : A → Set}
        → φ P ≡r φ P ∙ φ P
  φ≡φ∙φ {A} {P} = ⊆in aux1 , ⊆in aux2
    where
      aux1 : (a b : A) → φ P b a → (φ P ∙ φ P) b a
      aux1 a b (cons-φ (prf , pa))
        rewrite prf = a , cons-φ (refl , pa) , cons-φ (refl , pa)

      aux2 : (a b : A) → (φ P ∙ φ P) b a → φ P b a
      aux2 a b (c , cons-φ h1 , cons-φ h2) 
        = cons-φ (trans (p1 h1) (p1 h2) , p2 h1)

  {- 

  TODO :

  open import Rel.Reasoning.SubsetJudgement
  open import Rel.Reasoning.RelEq-Strategy using (rel-strat)
  open import Data.List using (List; []; _∷_)
  open import RW.RW (rel-strat ∷ [])

  φ-closure-r-1 : {A B : Set}{P : A → Set}{R S : Rel A B}
                → (R ∙ φ P ⊆ S ∙ φ P) ⇐ (R ∙ φ P ⊆ S)
  φ-closure-r-1 {P = P} {R = R} {S = S} 
    = begin
      R ∙ φ P ⊆ S ∙ φ P
    ⇐⟨ {!!} ⟩
      R ∙ φ P ∙ (φ P) ᵒ ⊆ S
    ⇐⟨ (tactic (by (quote φ≡φ∙φ))) ⟩
      R ∙ φ P ⊆ S
    ∎
  -}
