open import Prelude
open import Rel.Core
open import Rel.Core.Equality

module Rel.Relator where

  -- In order to encode recursive functors in dependent types
  -- we need W-types. A (W S P) can be read as the type
  -- of well-founded trees with S constructors of arity (P s) 
  -- for all (s : S).
  --
  data W (S : Set)(P : S → Set) : Set where
    sup : (s : S) → (P s → W S P) → W S P

  {-# TERMINATING #-}
  W-rec : ∀{c}{S : Set}{P : S → Set}
        → {C : W S P → Set c}
        → (c : (s : S) → (f : P s → W S P)
             → (h : (p : P s) → C (f p))
             → C (sup s f)
        ) → (x : W S P) → C x
  W-rec {C = C} c (sup s f) = c s f (W-rec {C = C} c ∘ f)

  -- Hopefully, it has been proved (by Abbot 2003 and Abbot 2004)
  -- that all polinomial functors are "strictly positive" and,
  -- therefore, have an initial algebra that correspond
  -- exactly to W S P.
  --
  -- This `typeclass` is intended to encode unary functors.
  -- The specific F is binary since the first argument is the type
  -- of the objects inside it. A couple examples are:
  --
  --  List A ⇒ F A X = 1 + A × X
  --  Nat    ⇒ F A X = 1 + X
  --
  record IsWFunctor1 (F : Set → Set → Set) : Set1 where
    field
      -- If F can be encoded as a W-type, we need it's (polymorphic) shape
      -- and positioning function.
      S : Set → Set
      P : {A : Set} → S A → Set
      
      -- We need in's and out's
      inF  : {A : Set} → F A (W (S A) P) → W (S A) P
      outF : {A : Set} → W (S A) P → F A (W (S A) P)

      -- And how it treats arrows.
      Fᵣ : {X A B : Set} → Rel A B → Rel (F X A) (F X B)

    -- TODO: lookup this theorem number!
    μF : Set → Set
    μF A = W (S A) P 

    inR : {A : Set} → Rel (F A (μF A)) (μF A)
    inR = fun inF

    outR : {A : Set} → Rel (μF A) (F A (μF A))
    outR = fun outF

  open IsWFunctor1 {{...}}


  -- A slight variant of W-rec rule allows us to build a Set (or a
  -- relation, for that matter) recursively.
  --
  {-# TERMINATING #-}
  W-rec-rel : {S : Set}{P : S → Set}{A : Set}
            → ((s : S) → (p : P s → W S P) → Rel (W S P) A → A → Set)
            → Rel (W S P) A
  W-rec-rel h a w = W-rec (λ s p c → h s p (W-rec-rel h) a) w

  -- 
  -- With some clever type translations we can encode a cata
  -- in a very relational fashion.
  --
  W-cata-F : {A B : Set}{F : Set → Set → Set}{{ prf : IsWFunctor1 F }}
             (R : Rel (F A B) B) → Rel (μF {F = F} A) B
  W-cata-F {A} {B} {F} R = W-rec-rel (λ s p h n → gene h n (sup s p))
    where
      -- Here, h is the relation built so far.
      -- By the cata-universsal law we can derive this gene
      gene : Rel (μF {F = F} A) B → Rel (μF {F = F} A) B
      gene h n l = (R ∙ Fᵣ h) n (outF l)
  
  -- Being a Relator is encoded as a separate structure.
  -- 
  record IsRelator (F : Set → Set → Set) {{ p : IsWFunctor1 F }} 
         : Set1 where 
    field
      fmap-id : ∀{B A} → (Fᵣ {F} {B} {A} {A} Id) ≡r Id

      fmap-∙ : ∀{I A B C}{R : Rel B C}{S : Rel A B}
             → Fᵣ {F} {I} (R ∙ S) ≡r Fᵣ R ∙ Fᵣ S

      fmap-ᵒ : ∀{I A B}{R : Rel A B}
             → Fᵣ {F} {I} (R ᵒ) ≡r (Fᵣ R) ᵒ

      fmap-⊆ : ∀{I A B}{R S : Rel A B}
             → R ⊆ S → Fᵣ {F} {I} R ⊆ Fᵣ S

  ----------------------
  -- * Catamorphism * --
  ----------------------

  -- We just need to wrap W-cata-F into a record. Same thing we did
  -- with the other relational constructs.
  record ⟦_⟧₁ {A B : Set}{F : Set → Set → Set}{{ prf : IsWFunctor1 F }}
              (R : Rel (F A B) B)(b : B)(μFa : μF {F = F} A) : Set
    where constructor cons-cata
          field un : W-cata-F R b μFa

  {-
  -- TODO: the universsal has to be proven for each F.
  --       we need some insight into F's structure to continue
  --       the proof, otherwise we're stuck at a W-cata-rel goal.
  -- And the universsal law
  cata-uni-1 : {A B : Set}{F : Set → Set → Set}
               {{ pF : IsWFunctor1 F }}{{ pR : IsRelator F }}
               {R : Rel (F A B) B}{X : Rel (μF {F = F} A) B}
             → X  ⊆ R ∙ Fᵣ X ∙ outR
             → X ⊆ ⟦ R ⟧₁
  cata-uni-1 (⊆in hip) 
    = ⊆in (λ la b bXa 
          → let (fab , bRfab , faμa , y , z) = hip la b bXa
            in cons-cata {!!}) -}
             
