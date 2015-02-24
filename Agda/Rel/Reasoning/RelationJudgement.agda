module Rel.Reasoning.RelationJudgement
       { A B : Set} 
     where

open import Data.Product using (_×_; ∃; _,_) renaming (proj₁ to p1; proj₂ to p2)
open import Rel.Core renaming (Rel to R)
open import Rel.Core.Equality
open import Relation.Binary
open import Level using (Level; zero; suc)

≡r-IsEquivalence : IsEquivalence (_≡r_ {A = A} {B = B})
≡r-IsEquivalence = record
  { refl  = ≡r-refl
  ; sym   = ≡r-sym
  ; trans = ≡r-trans
  }

⊆-IsPreorder : IsPreorder (_≡r_ {A = A} {B = B}) _⊆_
⊆-IsPreorder = record
  { isEquivalence = ≡r-IsEquivalence 
  ; reflexive     = _≡r_.p1
  ; trans         = ⊆-trans
  }

⊆-Preorder : Preorder _ _ _
⊆-Preorder = record
  { Carrier = R A B
  ; _≈_     = (_≡r_ {A = A} {B = B})
  ; _∼_     = _⊆_
  ; isPreorder = ⊆-IsPreorder
  }

≡r-IsPreorder : IsPreorder (_≡r_ {A = A} {B = B}) _≡r_
≡r-IsPreorder = record
  { isEquivalence = ≡r-IsEquivalence 
  ; reflexive     = id
  ; trans         = ≡r-trans
  }

≡r-Preorder : Preorder _ _ _
≡r-Preorder = record
  { Carrier = R A B
  ; _≈_     = (_≡r_ {A = A} {B = B})
  ; _∼_     = _≡r_
  ; isPreorder = ≡r-IsPreorder
  }

import Relation.Binary.PreorderReasoning as Pre

module ⊆-Reasoning where
  open Pre ⊆-Preorder public
    renaming
      (_∼⟨_⟩_ to _⊆⟨_⟩_
      ; _≈⟨_⟩_ to _≡r⟨_⟩_ 
      )

module ≡r-Reasoning where
  open Pre ≡r-Preorder public
    renaming
      (_∼⟨_⟩_ to _≡r⟨_⟩_
      )
