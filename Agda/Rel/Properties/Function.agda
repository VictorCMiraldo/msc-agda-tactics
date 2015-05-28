open import Prelude
open import Rel.Core
open import Rel.Core.Equality
open import Rel.Properties.Neutral

module Rel.Properties.Function where

  shunting-l-1 : {A B C : Set}{R : Rel A B}{S : Rel A C}{f : B → C}
               → R ⊆ (fun f) ᵒ ∙ S → fun f ∙ R ⊆ S
  shunting-l-1 {A} {B} {C} {R} {S} {f} (⊆in hip) = ⊆in aux
    where
      aux : (a : A)(c : C) → (fun f ∙ R) c a → S c a
      aux a c (b , cons-fun bfc , aRb) with hip a b aRb
      ...| h , cons-ᵒ (cons-fun cfb) , bSa
         rewrite sym bfc
               | sym cfb = bSa

  shunting-l-2 : {A B C : Set}{R : Rel A B}{S : Rel A C}{f : B → C}
               → fun f ∙ R ⊆ S → R ⊆ (fun f) ᵒ ∙ S
  shunting-l-2 {A} {B} {C} {R} {S} {f} (⊆in hip) = ⊆in aux
    where
      aux : (a : A) (b : B) → R b a → (fun f ᵒ ∙ S) b a
      aux a b bRa = f b , (cons-ᵒ (cons-fun refl)) 
                  , (hip a (f b) (b , (cons-fun refl , bRa)))

  shunting-r-1 : {A B C : Set}{R : Rel B C}{S : Rel A C}{f : B → A}
               → R ∙ (fun f) ᵒ ⊆ S → R ⊆ S ∙ (fun f)
  shunting-r-1 {A} {B} {C} {R} {S} {f} (⊆in hip) = ⊆in aux
    where
      aux : (a : B) (b : C) → R b a → (S ∙ fun f) b a
      aux b c cRb = f b
                  , (hip (f b) c (b , (cRb , cons-ᵒ (cons-fun refl))) 
                  , cons-fun refl)

  shunting-r-2 : {A B C : Set}{R : Rel B C}{S : Rel A C}{f : B → A}
               → R ⊆ S ∙ (fun f) → R ∙ (fun f) ᵒ ⊆ S
  shunting-r-2 {A} {B} {C} {R} {S} {f} (⊆in hip) = ⊆in aux
    where
      aux : (a : A) (b : C) → (R ∙ fun f ᵒ) b a → S b a
      aux a c (b , bRc , cons-ᵒ (cons-fun bfa)) with hip b c bRc
      ...| (x , sx , cons-fun xfb) 
         rewrite sym bfa
               | sym xfb = sx
      

  open import Rel.Reasoning.SubsetJudgement
  open import Rel.Reasoning.RelEq-Strategy using (rel-⊆-strat)
  open import RW.RW (rel-⊆-strat ∷ [])
  open ⊆-Reasoning

  f-isSimple : {A B : Set}{f : A → B}
             → isSimple (fun f)
  f-isSimple {f = f} = lemma unit
    where 
      lemma : tautology (isSimple (fun f))
      lemma = begin
           fun f ∙ fun f ᵒ ⊆ Id
         ⇐⟨ shunting-r-2 ⟩
           fun f ⊆ Id ∙ fun f
         ⇐⟨ (tactic (by (quote ∙-id-l))) ⟩
           fun f ⊆ fun f
         ⇐⟨ const ⊆-refl ⟩
           Unit
         ∎
