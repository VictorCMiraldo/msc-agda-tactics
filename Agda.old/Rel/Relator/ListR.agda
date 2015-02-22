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
      } where
        lemma-id : {A B C : Set} → Id + (Id * Id) ≡r Id {A ⊎ (B × C)}
        lemma-id {A} {B} {C}
          = subst (λ x → Id {A} + x ≡r Id) (≡r-promote (≡r-sym id*id≡id)) 
            id+id≡id

        lemma-∙ : {I A B C : Set} {R : Rel B C} {S : Rel A B}
                → Id {A} + (Id {B} * (R ∙ S)) ≡r Id + (Id * R) ∙ Id + (Id * S)
        lemma-∙ {I} {A} {B} {C} {R} {S} = ≡r-sym (coprod-uni-l (ι₁ ∙ Id) (ι₂ ∙ Id * (R ∙ S)) {!!} {!!})
          -- ⊆in aux1 , ⊆in {!!}
          where
            aux1 : (a : A ⊎ (B × A))(b : A ⊎ (B × C))
                 → (Id + (Id * (R ∙ S))) b a
                 → ((Id + (Id * R)) ∙ (Id + (Id * S))) b a
            aux1 (i1 x) b (cons-either un) 
              = i1 x , cons-either un 
              , cons-either (x , cons-fun refl , cons-fun refl)
            aux1 (i2 y) b (cons-either (w , c1 , cons-⟨,⟩ ((w1 , c21) , (w2 , (k , j) , c222)))) 
              = i2 (p1 w , k) 
              , cons-either (w , c1 , cons-⟨,⟩ ((w1 , p1 c21 , cons-fun (sym (fun.un (p1 c21)))) , k , p1 j , cons-fun refl)) 
              , cons-either ((w1 , k) , cons-fun (cong i2 (cong₂ _,_ (fun.un (p1 c21)) refl)) 
                            , cons-⟨,⟩ ((w1 , cons-fun refl , p2 c21) , w2 , p2 j , c222))

            i1-inj : ∀{a}{A B : Set a}{x y : A} → _≡_ {A = A ⊎ B} (i1 x) (i1 y) → x ≡ y
            i1-inj refl = refl

            aux2 : (a : A ⊎ (B × A))(b : A ⊎ (B × C))
                 → ((Id + (Id * R)) ∙ (Id + (Id * S))) b a
                 → (Id + (Id * (R ∙ S))) b a
            aux2 a b hip = {!!}
            {-
            aux2 (i1 x) (i1 y) (i1 z , (cons-either (h1 , p11 , p12) , cons-either (h2 , p21 , p22))) 
              = cons-either (y , cons-fun refl 
                            , cons-fun (trans (fun.un p22) (trans (i1-inj (fun.un p21)) (trans (fun.un p12) (i1-inj (fun.un p11))))))
            aux2 (i1 x) (i1 y) (i2 z , (h1 , cons-either un)) = {!!}
            aux2 (i1 x) (i2 y) hip = {!!}
            aux2 (i2 x) (i1 y) hip = {!!}
            aux2 (i2 x) (i2 y) hip = {!!}
            -}

        lemma-ᵒ : {I A B : Set} {R : Rel A B}
                → Id + (Id * (R ᵒ)) ≡r (Id + (Id * R)) ᵒ
        lemma-ᵒ = {!!}

        lemma-⊆ : {I A B : Set} {R : Rel A B} {S : Rel A B}
                → R ⊆ S → Id + (Id * R) ⊆ Id + (Id * S)
        lemma-⊆ = {!!}

  -- And, finally, the public list relator.
  ListR : Set → Set
  ListR = μF {F = L}


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
