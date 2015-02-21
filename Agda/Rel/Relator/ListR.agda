open import Prelude hiding (_*_) renaming (either to +-elim; _+_ to _+N_)
open import Coinduction

open import Rel.Core.Core
open import Rel.Relator
open import Rel.Core.Equality
open import Rel.Core.Coproduct
open import Rel.Core.Product

module Rel.Relator.ListR where

  open IsWFunctor1 {{...}}
  open IsRelator   {{...}}

  L : Set → Set → Set
  L A X = Unit ⊎ (A × X)

  private
    Ls : Set → Set
    Ls A = Unit ⊎ A

    Lp : {A : Set} (s : Ls A) → Set
    Lp = (+-elim (const ⊥) (const Unit))

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
      }


  module Example where

    open import Rel.Core.Correflexive
    
    sumR : Rel (μF {F = L} ℕ) ℕ
    sumR = ⟦ either ((φ (_≡_ zero)) ∙ Top) (fun (uncurry _+N_)) ⟧₁

    l1 : Lw ℕ
    l1 = cons (1 , nil)

    prf : sumR 1 l1
    prf = cons-cata $ i2 (1 , 0) 
        , cons-either (cons-fun refl) 
        , cons-either ((1 , 0) 
        , cons-fun refl 
        , cons-⟨,⟩ ((1 , cons-fun refl , cons-fun refl) 
                   , nil 
                   , (i1 unit , cons-either (0 , cons-φ (refl , refl) , unit) , cons-either (unit , cons-fun refl , cons-fun refl)) 
                   , cons-fun refl))
