open import Prelude hiding (_*_; _+_) renaming (either to +-elim)

open import Rel.Core
open import Rel.Core.Coproduct
open import Rel.Core.Product
open import Rel.Core.Correflexive

open import Rel.Core.Equality

open import Data.Product using (uncurry)
open import Data.List using (_∷_; [])

module Rel.CaseStudies.SelectionSort where

  module Generic
       {A : Set}
       (eqA : (a₁ a₂ : A) → Dec (a₁ ≡ a₂))
       (_≤_ : Rel A A) 
       (isConR : isConnected _≤_)
       (isASym : isAntiSymmetric _≤_)
       (isTrR  : isTransitive _≤_)
       (isRefl : isReflexive _≤_)
     where

     open import Rel.Relator
     open import Rel.Relator.List
     open import Rel.Relator.List.Defs

     open IsWFunctor1 {{...}}
     open IsRelator {{...}}

     ok : A × Lw A → Set
     ok (a₁ , x) = (a₂ : A) → elem {{ eq eqA }} x a₂ → a₂ ≤ a₁

     perm-preserves-ok : (l1 l2 : Lw A) → perm l1 l2 → (a : A) → ok (a , l1) → ok (a , l2)
     perm-preserves-ok l1 l2 hip a₁ aok a₂ a₂∈l2 
       = aok a₂ (⊆out (≡r-elim1 (perm-elem {{eq eqA}})) a₂ l1 (l2 , hip , a₂∈l2))

     ok-perm-natural : φ ok ∙ (Id * perm) ≡r (Id * perm) ∙ φ ok
     ok-perm-natural = ⊆in {!!} , ⊆in {!!}

     ordered : Rel (μ L A) (μ L A)
     ordered = ⟦ either nilR (consR ∙ φ ok) ⟧₁

     open import Rel.Properties.Monotonicity
     open import Rel.Properties.Basic
     open import Rel.Properties.Correflexive
     open import Rel.Properties.BiFunctor
     open import Rel.Reasoning.RelEq-Strategy
     open import RW.RW (rel-≡r-strat ∷ [])
     open import Rel.Reasoning.RelationJudgement   

     cata-⊥ : {A : Set}{F : Set → Set → Set}{{pF : IsWFunctor1 F}}{{pR : IsRelator F}}{R : Rel (F A (μ F A)) (μ F A)}
            → (a b : μ F A) → (R b (outF a) → ⊥) → ⟦ R ⟧₁ b a → ⊥
     cata-⊥ a b hip = {!!}

     perm-idp : perm ≡r perm ᵒ
     perm-idp = cata-uni-2 {!!} , cata-uni-1 {!!}
       where
         aux1 : either nilR add ∙ (Id + (Id * (perm ᵒ))) ∙ outR ⊆ perm ᵒ
         aux1 = {!!}

     ordered-idp : ordered ≡r ordered ᵒ
     ordered-idp = {!!}

     {-
     
     prf1 : ordered ∙ perm ≡r (perm ∙ ⟦ either nilR (consR ∙ φ ok) ⟧₁) ᵒ
     prf1 = begin
              ordered ∙ perm
          ≡r⟨ ≡r-cong (λ i → i ∙ perm) ordered-idp ⟩
              ordered ᵒ ∙ perm
          ≡r⟨ ≡r-cong (λ i → ordered ᵒ ∙ i) perm-idp ⟩
              ordered ᵒ ∙ perm ᵒ
          ≡r⟨ ᵒ-∙-distr ⟩
              (perm ∙ ordered) ᵒ
          ≡r⟨ ≡r-refl ⟩
              (perm ∙ ⟦ either nilR (consR ∙ φ ok) ⟧₁) ᵒ
          ∎
        where open ≡r-Reasoning  

     select : Rel (Lw A) (A × Lw A)
     select = {!!}

     selectLemma : select ⊆ φ ok ∙ consR ᵒ ∙ perm
     selectLemma = {!!}

     fusionLemma2 : select ᵒ ∙ (Id * perm) ⊆ perm ∙ consR ∙ φ ok
     fusionLemma2 = begin
           select ᵒ ∙ Id * perm
        ⊆⟨ ∙-mono (ᵒ-mono selectLemma) ⊆-refl ⟩
           (φ ok ∙ consR ᵒ ∙ perm) ᵒ ∙ Id * perm
        ≡r⟨ ≡r-cong (λ i → i ∙ Id * perm) (≡r-sym ᵒ-∙-distr3) ⟩
           (perm ᵒ ∙ (consR ᵒ) ᵒ ∙ φ ok ᵒ) ∙ Id * perm
        ≡r⟨ ≡r-cong (λ i → (perm ᵒ ∙ i ∙ φ ok ᵒ) ∙ Id * perm) ᵒ-idp ⟩
           (perm ᵒ ∙ consR ∙ φ ok ᵒ) ∙ Id * perm
        ≡r⟨ ≡r-cong (λ i → (i ∙ consR ∙ φ ok ᵒ) ∙ Id * perm) (≡r-sym perm-idp) ⟩
            (perm ∙ consR ∙ φ ok ᵒ) ∙ Id * perm
        ≡r⟨ ≡r-cong (λ i → (perm ∙ consR ∙ i) ∙ Id * perm) (≡r-sym φ≡φᵒ) ⟩
            (perm ∙ consR ∙ φ ok) ∙ Id * perm
        ≡r⟨ ≡r-sym ∙-assoc-join ⟩
            (perm ∙ consR) ∙ φ ok ∙ Id * perm
        ≡r⟨ ≡r-cong (λ i → (perm ∙ consR) ∙ i) ok-perm-natural ⟩
           (perm ∙ consR) ∙ Id * perm ∙ φ ok
        ≡r⟨ ∙-assoc-join ⟩
           (perm ∙ consR ∙ Id * perm) ∙ φ ok
        ≡r⟨ ≡r-sym (≡r-cong (λ i → i ∙ φ ok) permLemma) ⟩
          (perm ∙ consR) ∙ φ ok
        ≡r⟨ ∙-assoc ⟩
           perm ∙ consR ∙ φ ok
        ∎
       where open ⊆-Reasoning

     fusionLemma1 : {B : Set} → nilR ∙ Id {B} ⊆ perm ∙ nilR
     fusionLemma1 {B} = ⊆-trans (≡r-elim2 (∙-id-r nilR)) (⊆in aux)
       where
         aux : (a : B)(b : Lw A) → nilR b a → (perm ∙ nilR) b a
         aux a b (.(i1 unit) , (cons-fun c1 , unit , (cons-fun refl , unit))) 
           with inL {A = Ls A} (i1 unit)
         aux a .(sup (i1 unit) (λ ())) (._ , (cons-fun refl , unit , (cons-fun refl , unit))) 
           | sup s x 
           = nil , cons-cata ((i1 unit) , ((cons-either ((i1 unit) , ((cons-fun refl) , (unit , (cons-fun refl , unit))))) 
                                        ,  (cons-either (unit , (cons-fun refl , cons-fun refl))))) 
           , (i1 unit) , ((cons-fun refl) , unit , (cons-fun refl , unit))

     prf2 : ⟦ either nilR (select ᵒ) ⟧₁ ᵒ 
          ⊆ (perm ∙ ⟦ either nilR (consR ∙ φ ok) ⟧₁) ᵒ
     prf2 = ᵒ-mono (cata-fusion-1 (
          begin
            either nilR (select ᵒ) ∙ Id + (Id * perm)
          ≡r⟨ either-+-abs ⟩
             either (nilR ∙ Id) (select ᵒ ∙ Id * perm)
          ⊆⟨ lemma ⟩
            either (perm ∙ nilR) (perm ∙ consR ∙ φ ok)
          ≡r⟨ ≡r-sym either-abs ⟩
             perm ∙ either nilR (consR ∙ φ ok)
          ∎
       ))
       where
         open ⊆-Reasoning

         lemma : either (nilR ∙ Id) (select ᵒ ∙ Id * perm)
               ⊆ either (perm ∙ nilR) (perm ∙ consR ∙ φ ok)
         lemma = coprod-uni-l-aux1 (perm ∙ nilR) (perm ∙ consR ∙ φ ok) 
                 (⊆-trans (≡r-elim1 ι₁-cancel) fusionLemma1) 
                 (⊆-trans (≡r-elim1 ι₂-cancel) fusionLemma2)
     
  
  
  
  -}
