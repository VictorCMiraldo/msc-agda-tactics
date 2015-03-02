open import Prelude hiding (_*_; _+_) renaming (either to +-elim)

open import Rel.Core
open import Rel.Core.Equality
open import Rel.Core.Product
open import Rel.Core.Coproduct
open import Rel.Relator

open import Rel.Reasoning.RelEq-Strategy
open import RW.RW (rel-strat ∷ [])

module Rel.Relator.List where

  -- A List encoded as a W-type
  private
    L : Set → Set → Set
    L A X = Unit ⊎ (A × X)

    Ls : Set → Set
    Ls = _⊎_ Unit

    Lp : {A : Set} → Ls A → Set
    Lp = +-elim (const ⊥) (const Unit)

  Lw : Set → Set
  Lw A = W (Ls A) Lp

  nil : {A : Set} → Lw A
  nil = sup (i1 unit) (λ ())

  cons : {A : Set} → A × Lw A → Lw A
  cons (h , t) = sup (i2 h) (const t)

  inL : {A : Set} → L A (Lw A) → Lw A
  inL = +-elim (const nil) cons

  outL : {A : Set} → Lw A → L A (Lw A)
  outL (sup (i1 x) x₁) = i1 unit
  outL (sup (i2 y) x) = i2 (y , x unit)

  nilR : {A B : Set} → Rel B (Lw A)
  nilR = fun inL ∙ ι₁ ∙ Top

  consR : {A : Set} → Rel (A × Lw A) (Lw A)
  consR = fun inL ∙ ι₂

  open IsWFunctor1 {{...}}
  open IsRelator {{...}}

  instance
    IsWFunctor1-L : IsWFunctor1 L
    IsWFunctor1-L = record
      { S = Ls
      ; P = Lp
      ; inF = inL
      ; outF = outL
      ; Fᵣ = λ R → Id + (Id * R)
      }
    
    IsRelator-L : IsRelator L
    IsRelator-L = record
      { fmap-id = {!!}
      ; fmap-∙  = {!!}
      ; fmap-ᵒ  = {!!}
      ; fmap-⊆  = {!!}
      } where
        open import Rel.Properties.BiFunctor
        open import Rel.Properties.Neutral
  
        lemma-id : {A B C : Set} → Id + (Id * Id) ≡r Id {A ⊎ (B × C)}
        lemma-id {A} {B} {C}
          = subst (λ x → Id {A} + x ≡r Id) (≡r-promote (≡r-sym *-id)) +-id

        lemma-∙ : {I A B C : Set} {R : Rel B C} {S : Rel A B}
                → Id {A} + (Id {B} * (R ∙ S)) ≡r Id + (Id * R) ∙ Id + (Id * S)
        lemma-∙ {I} {A} {B} {C} {R} {S} 
          = ≡r-sym (coprod-uni-l (ι₁ ∙ Id) (ι₂ ∙ Id * (R ∙ S)) 
                                 (≡r-sym aux1) {!!})
          where
            open import Rel.Reasoning.RelationJudgement         
            open ≡r-Reasoning

            aux1 : (Id + (Id {B} * R) ∙ Id + (Id * S)) ∙ ι₁ ≡r ι₁ ∙ Id {A}
            aux1 = begin 
                 (Id + (Id {B} * R) ∙ Id + (Id * S)) ∙ ι₁
              ≡r⟨ ≡r-cong (λ s → s ∙ ι₁) +-bi-functor ⟩ 
                 ((Id ∙ Id) + (Id * R ∙ Id * S)) ∙ ι₁
              ≡r⟨ ≡r-sym ι₁-natural ⟩ 
                 ι₁ ∙ (Id ∙ Id)
              ≡r⟨ ≡r-cong (_∙_ ι₁) (≡r-sym (∙-id-r Id)) ⟩
                 ι₁ ∙ Id
              ∎ 

            aux2 : (Id {A} + (Id {B} * R) ∙ Id + (Id * S)) ∙ ι₂ ≡r ι₂ ∙ Id * (R ∙ S)
            aux2 = begin 
                 (Id + (Id * R) ∙ Id + (Id * S)) ∙ ι₂
              ≡r⟨ ≡r-cong (λ s → s ∙ ι₂) +-bi-functor ⟩ 
                 (Id ∙ Id) + (Id * R ∙ Id * S) ∙ ι₂
              ≡r⟨ ≡r-sym ι₂-natural ⟩ 
                 ι₂ ∙ Id * R ∙ Id * S
              ≡r⟨ ≡r-cong (_∙_ ι₂) {!!} ⟩
                  {!ι₂ ∙ (Id * Id) ∙ (R * S)!}
              ≡r⟨ {!!} ⟩
                 ι₂ ∙ Id * (R ∙ S)
              ∎ 

          
  
  l1 : Lw ℕ
  l1 = cons (1 , nil)

  l2 : Lw ℕ
  l2 = cons (1 , cons (2 , nil))

  prefix : Rel (Lw ℕ) (Lw ℕ)
  prefix = ⟦ either nilR (nilR ∪ consR) ⟧₁

  prf : prefix l1 l2
  prf = cons-cata (i2 (1 , nil) 
      , (cons-either (cons-∪ (i2 (i2 (1 , nil) , (cons-fun refl) , (cons-fun refl)))) 
      , (cons-either ((1 , nil) 
      , (cons-fun refl , (cons-⟨,⟩ ((1 , ((cons-fun refl) , (cons-fun refl))) 
        , cons (2 , nil) , (((i2 (2 , nil)) , ((cons-either (cons-∪ (i1 (i1 unit , cons-fun refl , unit , cons-fun refl , unit)))) 
      , (cons-either ((2 , nil) , (cons-fun refl , cons-⟨,⟩ ((2 , ((cons-fun refl) , (cons-fun refl))) 
                     , nil , (((i1 unit) , ((cons-either (i1 unit , cons-fun refl , unit , cons-fun refl 
      , unit)) , (cons-either (unit , cons-fun refl , cons-fun refl)))) , cons-fun refl))))))) , cons-fun refl))))))))
