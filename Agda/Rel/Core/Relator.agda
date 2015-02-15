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

open import Coinduction

module Rel.Core.Relator where


  ----------------------
  -- * Functor Laws * --
  ----------------------

  record IsFunctor (F : Set → Set) : Set1 where
    constructor functor
    field fmap : {A B : Set}(f : A → B) → F A → F B

  -- Least functor fixed point.
  {-# TERMINATING #-}
  μ : (F : Set → Set) → Set
  μ F = F (Rec (♯ μ F))

  -- Encapsulate a Rec back to a μ.
  encap : {F : Set → Set}{{ _ : IsFunctor F }} 
        → F (Rec (♯ μ F)) → F (μ F)
  encap ⦃ functor m ⦄ f = m unfold f

  record IsRelator (F : Set → Set){{ _ : IsFunctor F }} : Set1 where
    field
      -- A catamorphism only exists if there exists an initial F-algebra.
      -- therefore, we need to give one such algebra.
      inF : Rel (F (μ F)) (μ F)

      -- Describes F's effect on arrows.
      Fᵣ : ∀{A B} → Rel A B → Rel (F A) (F B)

      -- Relator properties follow:

      fmap-id : ∀{A} → (Fᵣ {A} {A} Id) ≡r Id

      fmap-∙  : ∀{A B C}{R : Rel B C}{S : Rel A B} 
              → Fᵣ (R ∙ S) ≡r Fᵣ R ∙ Fᵣ S

      fmap-ᵒ  : ∀{A B}{R : Rel A B}
              → Fᵣ (R ᵒ) ≡r (Fᵣ R) ᵒ
    
      fmap-⊆  : ∀{A B}{R S : Rel A B}
              → R ⊆ S → Fᵣ R ⊆ Fᵣ S

  open IsRelator {{...}}

  ----------------------
  -- * Catamorphism * --
  ----------------------

  -- Defining a catamorphism in Agda is quite tough.
  -- If we encapsulate it in a record, we need to define
  -- it in terms of something else. From the cata-universal,
  -- we can see that this something else involves the cata itself,
  -- so we need the --type-in-type option, which renders Agda inconsistent.
  --
  -- Another option, though, is to defie it in terms of postulates.
  -- It shouldn't be a problem to prove stuff, since the IsRelator
  -- object guarantees that both F is a relator and there exists
  -- an initial algebra (α : Σ (μ F) (μ F) ⟵ F (μ F)), therefore
  -- all we allow a user to do is theoretically sound.
  --
  -- Proofs involving cata's usually goes in terms of universal 
  -- fusion and cancelation, so we don't need anything else.
  --
  postulate
    cata : {A : Set}{F : Set → Set}{{ _ : IsFunctor F}}{{ prf : IsRelator F }}
           (R : Rel (F A) A) → Rel (μ F) A

    cata-uni : {A : Set}{F : Set → Set}{{ _ : IsFunctor F }}{{ prf : IsRelator F }}
               {R : Rel (F A) A} → cata R ∙ inF ≡r R ∙ Fᵣ (cata R)
    
