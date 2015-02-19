open import Prelude renaming (_+_ to _+N_; _*_ to _*N_)
open import Rel.Core.Core
open import Rel.Core.Coproduct renaming (either to +-elim)
open import Rel.Core.Product
open import Rel.Core.Correflexive
open import Rel.Core.HOTT
open import Rel.Core.Core
open import Rel.Core.Equality

module Wtypes where

  data W (S : Set)(P : S → Set) : Set where
    sup : (s : S) → (P s → W S P) → W S P

  {-# TERMINATING #-}
  W-rec : ∀{c}{S : Set}{P : S → Set}
        → (C : W S P → Set c) -- conclusion
        -- parameter:
        → (c : (s : S)  -- Given a shape
             → (f : P s → W S P) -- a bunch of kids
             → (h : (p : P s) → C (f p)) -- and a C for each kid
             → C (sup s f)) -- does C hold?
        → (x : W S P) → C x -- C always holds.
  W-rec C c (sup s f) = c s f (W-rec C c ∘ f)

  -- A Set-valued version
  W-rec-set : {S : Set}{P : S → Set}
            → ((s : S) → (P s → W S P) → (P s → Set) → Set)
            → W S P → Set
  W-rec-set h = W-rec (const Set) h

  -- Non dependent version
  {-# TERMINATING #-}
  W-rec' : {S : Set}{P : S → Set}{A : Set}
         → ((s : S) → (P s → W S P) → (P s → A) → A)
         → W S P → A
  W-rec' f (sup s p) = f s p (W-rec' f ∘ p)

  -- Beeing a W-functor is having a Shape and Positioning function,
  -- and, being able to go from one repr to another.
  --
  -- Fᵣ just describes the functor effect on arrows.
  -- 
  -- lambek should probably disappear, since we're guaranteed
  -- the existence of the initial-algebra, Lambek's lemma is a mere
  -- consequence. It's there because in older versions I used
  -- "rewrite lambek" to open and close a functor.
  record IsWFunctor1 (F : Set → Set → Set) : Set1 where
    field
      S : Set → Set
      P : {A : Set} → S A → Set
      
      inF  : {A : Set} → F A (W (S A) P) → W (S A) P
      outF : {A : Set} → W (S A) P → F A (W (S A) P)

      lambek : {A : Set} → W (S A) P ≡ F A (W (S A) P)

      Fᵣ : {X A B : Set} → Rel A B → Rel (F X A) (F X B)

    μF : Set → Set
    μF A = W (S A) P 

  open IsWFunctor1 {{...}}

  -- Catamorphism definition.
  --   The idea is to express the parameter to W-rec-set
  --   as a transformation of R... not going so good.
  --
  -- Module WListPre gives a less general example.
  record ⟦_⟧₁ {A B : Set}{F : Set → Set → Set}{{ prf : IsWFunctor1 F }}
              (R : Rel (F A B) B)(b : B)(μFa : μF {F = F} A) : Set1
    where constructor cons-cata
          field un : W-rec-set (λ s p f → R b {!!}) μFa

  -- Some experiments with lists.
  module WListPre where
    
    L : Set → Set → Set
    L A X = Unit ⊎ (A × X)

    Ls : Set → Set
    Ls A = Unit ⊎ A

    Lp : {A : Set} (s : Ls A) → Set
    Lp = (either (const ⊥) (const Unit))

    Lw : Set → Set
    Lw A = W (Ls A) Lp

    nil : {A : Set} → Lw A
    nil = sup (i1 unit) (λ ())

    cons : {A : Set} → A × Lw A → Lw A
    cons (h , t) = sup (i2 h) (const t)

    inL : {A : Set} → L A (Lw A) → Lw A
    inL = either (const nil) cons

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
        { S = λ I → Unit ⊎ I
        ; P = either (const ⊥) (const Unit)
        ; inF = inL
        ; outF = outL
        ; lambek = {!!}
        ; Fᵣ = λ R → Id + (Id * R)
        }

    l1 : Lw ℕ
    l1 = cons (4 , cons (3 , cons (2 , cons (1 , nil))))

    l2 : Lw ℕ
    l2 = cons (4 , cons (3 , nil))

    l3 : Lw ℕ
    l3 = cons (1 , nil)

    sumF : μF {F = L} ℕ → ℕ
    sumF = W-rec' gene
      where
        mS : Set
        mS = Unit ⊎ ℕ

        mP : mS → Set
        mP = either (const ⊥) (const Unit)

        gene : (s : mS) → (mP s → W mS mP) → (mP s → ℕ) → ℕ
        gene (i1 x) p h = zero
        gene (i2 y) p h = h unit +N y

    -- although this could be writen as (fun sumF),
    -- the objective is to explore how to define it in general terms.
    sumR : ℕ → (μF {F = L} ℕ) → Set
    sumR n l = W-rec-set {!!} l
      where
        f : Rel Unit ℕ
        f = (φ (_≡_ zero)) ∙ Top
  
        g : Rel (ℕ × ℕ) ℕ
        g = fun (uncurry _+N_)

        -- this is the relational gene for the "sumR"
        -- +-elim f g = [ f , g ]
        --
        geneR : Rel (L ℕ ℕ) ℕ
        geneR = +-elim f g

        -- The first branch is pretty simple. The second is a problem.
        gene : ℕ → (s : Unit ⊎ ℕ)
             → (Lp s → Lw ℕ) → (Lp s → Set) → Set
        gene n (i1 x) p h = f n unit
        -- here, I need to somehow get the recursive result, the induction
        -- hypothesis h is a set, and have to be used on the right-hand side,
        -- otherwise we're not traversing the whole list.
        gene n (i2 y) p h = h unit × g n {!!}
