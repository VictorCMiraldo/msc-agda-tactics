module Rel.Functors where

open import Data.Bool using (Bool; true; false)
open import Relation.Binary.PropositionalEquality
open import Data.Product using (_×_; ∃; _,_) renaming (proj₁ to p1; proj₂ to p2)
open import Data.Sum using (_⊎_; [_,_]) renaming (inj₁ to i1; inj₂ to i2; [_,_]′ to case)
open import Function using (id; _∘_)
open import Category.Functor

open import Rel.Core

open import Data.Unit
open import Data.Empty

open import Level

----------------------
-- * Functor Laws * --
----------------------

M : ∀{A : Set} → A → A ⊎ Unit
M a = i1 a

𝓜 : ∀{A B} → Rel A B → Rel (A ⊎ Unit) (B ⊎ Unit)
𝓜 r (i1 a) (i1 b) = r a b
𝓜 r _ (i2 _)      = ⊥
𝓜 r (i2 _) _      = ⊥

record IsFunctor {α}(F : Set α → Set α) : Set (suc α) where
  field
    fmap-id : {A : Set α} → Unit --  F (id {A = A}) ≡ id {A = F A}

