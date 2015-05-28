open import Prelude

open import Rel.Core
open import Rel.Core.Correflexive
open import Rel.Core.Equality

open import Rel.Reasoning.SubsetJudgement
open import Rel.Reasoning.RelEq-Strategy using (rel-⊆-strat)
open import RW.RW (rel-⊆-strat ∷ [])
open ⊆-Reasoning

module Rel.Examples.Ex01 where

  -- f ∙ φ is simple
  lemma-1 : {A B : Set}{f : A → B}{p : A → Set}
          → img (fun f ∙ φ p) ⊆ Id
  lemma-1 {B = B} {f = f} {p = p} = ⊆in aux
    where
      aux : (b₁ b₂ : B) → (img (fun f ∙ φ p)) b₂ b₁ → Id b₂ b₁
      aux b1 b2 (a , (.a , cons-fun f1 , cons-φ (refl , pb')) 
            , cons-ᵒ (.a , cons-fun f2 , cons-φ (refl , _))) 
        rewrite f1 | f2 = cons-fun refl

  lemma-2 : {A B : Set}{R : Rel A B}{S : Rel B B}
          → img R ⊆ S × img R ⊆ Id
          → ρ R ⊆ S
  lemma-2 {A} {B} {R} {S} (⊆in h1 , ⊆in h2) = ⊆in aux
    where
      aux : (a b : B) → ρ R b a → S b a
      aux b1 .b1 (cons-ρ (i , refl)) = h1 b1 b1 i
  
  -- Inavariant Preservation
  open import Rel.Properties.Function
  open import Rel.Properties.Correflexive
  open import Rel.Properties.Basic

  open import RW.Data.RTrie
  open import RW.Language.RTermTrie

  proof-db : RTrie
  proof-db = unquote (quoteTerm (p2
           -- $ add-action (quote ∙-assoc-join')
           $ add-action (quote ᵒ-∙-distr)
           -- For some reason, whenever our action receives no 
           -- explicit parameters, auto fails. TODO: find out why.
           $ add-action (quote φ≡φᵒ')
           $ add-action (quote φ≡φ∙φ)
           $ 0 , BTrieEmpty))

  open Auto proof-db (const $ rdef $ quote _≡r_)           
  
  inv-preserv : {A B : Set}{pa : A → Set}{pb : B → Set}{f : A → B}
              → (ρ (fun f ∙ φ pa) ⊆ φ pb) ⇐ (fun f ∙ φ pa ⊆ φ pb ∙ fun f)
  inv-preserv {A} {B} {pa} {pb} {f}
    = begin
       ρ (fun f ∙ φ pa) ⊆ φ pb
    ⇐⟨ lemma-2 ⟩
      (img (fun f ∙ φ pa) ⊆ φ pb × img (fun f ∙ φ pa) ⊆ Id)
    ⇐⟨ (λ x → x , lemma-1) ⟩
       img (fun f ∙ φ pa) ⊆ φ pb
    ⇐⟨ (tactic (by (quote ᵒ-∙-distr))) ⟩
       (fun f ∙ φ pa) ∙ (φ pa) ᵒ ∙ (fun f) ᵒ ⊆ φ pb
    ⇐⟨ ≡r-subst (λ x → x ⊆ φ pb) (≡r-sym ∙-assoc-join) ⟩
      (fun f ∙ φ pa ∙ (φ pa) ᵒ ) ∙ (fun f) ᵒ ⊆ φ pb
    ⇐⟨ (tactic auto) ⟩
      (fun f ∙ (φ pa ∙ φ pa)) ∙ (fun f) ᵒ ⊆ φ pb
    ⇐⟨ (tactic (by (quote φ≡φ∙φ))) ⟩
      (fun f ∙ φ pa) ∙ fun f ᵒ ⊆ φ pb
    ⇐⟨ shunting-r-2 ⟩
      fun f ∙ φ pa ⊆ φ pb ∙ fun f
    ∎
