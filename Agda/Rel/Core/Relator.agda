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
    field fmap  : {A B : Set}(f : A → B) → F A → F B

  open IsFunctor {{...}}

  -- Opening it as a polinimal functor. 
  -- This way we can be sure we can open and close,
  -- pretty much like an F-algebra's in.
  {-
  record IsShapely (F : Set → Set){{ _ : IsFunctor F }} : Set1 where
    constructor shapely
    field
      -- Hunch: Beeing `Shapely`, by my definition, does not imply Polynomial.
      ß : Set → Set → Set
      inF  : {A : Set} → ß (F A) A → F A
      outF : {A : Set} → F A → ß (F A) A
      lambek : {A : Set} → F A ≡ ß (F A) A

  open IsShapely {{...}}
  -}

  record IsRelator (F : Set → Set)
                   : Set1 where
    field
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

  instance
    Id-IsFunctor : IsFunctor (λ z → z)
    Id-IsFunctor = functor (λ f a → f a)

  

  ----------------------
  -- * Catamorphism * --
  ----------------------

  cast-dom : {A A′ B : Set} → A ≡ A′ → Rel A B → Rel A′ B
  cast-dom prf r rewrite prf = r

  cast-ran : {A B B′ : Set} → B ≡ B′ → Rel A B → Rel A B′
  cast-ran prf r rewrite prf = r

  cast : {A A′ B B′ : Set} → A ≡ A′ → B ≡ B′ → Rel A B → Rel A′ B′
  cast prfA prfB r 
    rewrite prfA
          | prfB
          = r

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
  -- ?? All shapely functor has initial algebra ?? Sokolova.
  --
  -- Proofs involving cata's usually goes in terms of universal 
  -- fusion and cancelation, so we don't need anything else.
  --
  record cata {A B : Set}{F : Set → Set}{{ pR : IsRelator F }}
              (b : B)(fa : F A) : Set1
    where constructor cons-cata
          field gene : Set → Set
                un   : {B : Set} → Rel (gene B) B

  open cata {{...}}

  cata-uni : {A B : Set}{F : Set → Set}{{ pR : IsRelator F }}
             cata R ∙ ? ≡r R ∙ ?

  {-

  postulate
    cata : {A B : Set}{F : Set → Set}
           {{pF : IsFunctor F}}{{ pR : IsRelator F }}
           (R : gene A B) → Rel (F A) B

    cata-uni-ß : {A B : Set}{F : Set → Set}
               {{pF : IsFunctor F}}{{ pR : IsRelator F }}
               {R : gene A B } 
             →  (cata {A} {B} {F} R ∙ fun inF) 
             ≡r {!!}
  -}
    
