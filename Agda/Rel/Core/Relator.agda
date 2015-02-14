open import Data.Bool using (Bool; true; false)
open import Relation.Binary.PropositionalEquality
open import Data.Product using (_×_; ∃; _,_) renaming (proj₁ to p1; proj₂ to p2)
open import Data.Sum using (_⊎_; [_,_]) renaming (inj₁ to i1; inj₂ to i2; [_,_]′ to case)
open import Function using (id; _∘_)
open import Category.Functor

open import Rel.Core.Core
open import Rel.Core.Equality

open import Data.Unit
open import Data.Empty

open import Level

module Rel.Core.Relator where


  ----------------------
  -- * Functor Laws * --
  ----------------------

  record IsRelator (F : Set → Set) : Set1 where
    field
      Fᵣ : ∀{A B} → Rel A B → Rel (F A) (F B)

      fmap-id : ∀{A} → (Fᵣ {A} {A} Id) ≡r Id

      fmap-∙  : ∀{A B C}{R : Rel B C}{S : Rel A B} 
              → Fᵣ (R ∙ S) ≡r Fᵣ R ∙ Fᵣ S

      fmap-ᵒ  : ∀{A B}{R : Rel A B}
              → Fᵣ (R ᵒ) ≡r (Fᵣ R) ᵒ
    
      fmap-⊆  : ∀{A B}{R S : Rel A B}
              → R ⊆ S → Fᵣ R ⊆ Fᵣ S

  open IsRelator {{...}}
  
