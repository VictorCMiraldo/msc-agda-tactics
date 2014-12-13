module Rel.Core.HOTT where

open import Relation.Binary.PropositionalEquality
open import Data.Product using (Σ; _×_; ∃; _,_) renaming (proj₁ to p1; proj₂ to p2)
open import Data.Sum using (_⊎_; [_,_]) renaming (inj₁ to i1; inj₂ to i2; [_,_]′ to case)
open import Function using (id; _∘_)

open import Data.Unit using (Unit; unit)
open import Data.Empty using (⊥; ⊥-elim)

--------------------------
-- * Base Definitions * --
--------------------------

isProp : ∀{a} → Set a → Set a
isProp P = (p₁ p₂ : P) → p₁ ≡ p₂

isContr : ∀{a} → Set a → Set a
isContr A = Σ A (λ x → (y : A) → x ≡ y)

prop-contr : {A : Set} → isProp A → A → isContr A
prop-contr prf a = a , prf a

contr-prop : {A : Set} → isContr A → isProp A
contr-prop (a , prf) = λ p₁ p₂ → trans (sym (prf p₁)) (prf p₂)

-- Homotopy definition
_~_ : {A : Set}{B : A → Set}(f g : (x : A) → B x) → Set
f ~ g = ∀ x → f x ≡ g x

-- A homotopy is a equivalence relation
~-refl : {A : Set}{B : A → Set}{f : (x : A) → B x} → f ~ f
~-refl = λ x → refl

~-sym : {A : Set}{B : A → Set}{f g : (x : A) → B x} → f ~ g → g ~ f
~-sym prf = λ x → sym (prf x)

~-trans : {A : Set}{B : A → Set}{f g h : (x : A) → B x}
        → f ~ g → g ~ h → f ~ h
~-trans fg gh = λ x → trans (fg x) (gh x)

-- Equivalence definition in terms of quasi-inverses.
isequiv : {A B : Set}(f : A → B) → Set
isequiv f = ∃ (λ g → ((f ∘ g) ~ id) × ((g ∘ f) ~ id))

-- Homotopy Fiber def.
hfiber : {A B : Set}(f : A → B)(b : B) → Set
hfiber {A} f b = Σ A (λ a → f a ≡ b)

-- Weak equivalence def.
weak-eq : {A B : Set}(f : A → B) → Set
weak-eq {B = B} f = (b : B) → isContr (hfiber f b)

-- univalence
_≈_ : (A B : Set) → Set
A ≈ B = ∃ (λ f → isequiv {A = A} {B = B} f)

-- which is also a equivalence relation
≈-refl : {A : Set} → A ≈ A
≈-refl = id , id , (λ _ → refl) , (λ _ → refl)

≈-sym : {A B : Set} → A ≈ B → B ≈ A
≈-sym (ab , (ba , isequiv-ab)) 
  = ba , ab , p2 isequiv-ab , p1 isequiv-ab

≈-trans : {A B C : Set} → A ≈ B → B ≈ C → A ≈ C
≈-trans (ab , (ba , isequiv-ab)) (bc , (cb , isequiv-cb))
  = bc ∘ ab , ba ∘ cb 
  , quasi-inv cb bc ba ab (p1 isequiv-cb) (p1 isequiv-ab) 
  , quasi-inv ab ba bc cb (p2 isequiv-ab) (p2 isequiv-cb)
  where
    quasi-inv : {A B C : Set}
                  (f : A → B)(f̅ : B → A)(g : B → C)(g̅ : C → B) 
                → ((f̅ ∘ f) ~ id) → ((g̅ ∘ g) ~ id)
                → (f̅ ∘ g̅ ∘ g ∘ f) ~ id
    quasi-inv f if g ig prff prfg x 
      rewrite prfg (f x) 
            | prff x 
            = refl

------------------------
-- The following two lemmas allows us to prove a proposition is either true or false.
                
-- This allows us to completely forget the contents of a proof for a 
-- given proposition.
lemma-332 : {P : Set} → isProp P → (p₀ : P) → P ≈ Unit
lemma-332 {P = P} prop prf = isequiv-p→1 prop prf
  where
    quasi-inv-1 : {P : Set}(f : P → Unit) → (g : Unit → P) → (f ∘ g) ~ id
    quasi-inv-1 f g unit with g unit | f (g unit)
    ...| gu | unit = refl

    quasi-inv-2 : {P : Set} → isProp P → (f : Unit → P) → (g : P → Unit) → (f ∘ g) ~ id
    quasi-inv-2 prf f g x with g x
    ...| gx with f gx
    ...| fgx = prf fgx x

    isequiv-p→1 : {P : Set} → isProp P → P → Σ (P → Unit) (λ f → isequiv f)
    isequiv-p→1 prf p₀ 
      = let
        p1 = λ _ → unit
        1p = λ _ → p₀
      in p1 , 1p , quasi-inv-1 p1 1p , quasi-inv-2 prf 1p p1

-- Also a negative variant of lemma 3.3.2, which will be very usefull.
¬lemma-332 : {P : Set} → isProp P → (P → ⊥) → P ≈ ⊥
¬lemma-332 {P} prp f = f , (λ ()) , (λ ()) , (⊥-elim ∘ f) 

--------------------------
-- * Univalence Axiom * --
--------------------------

postulate
  -- Following the steps of HoTT in Agda, we'll just postulate the univalence axiom.
  ≈-to-≡ : {A B : Set} → (A ≈ B) → A ≡ B


----------------------------------------------------
-- * Univalence implies function extensionality * --
----------------------------------------------------

-- the proof is from:
--   http://homotopytypetheory.org/2014/02/17/another-proof-that-univalence-implies-function-extensionality/

Paths : (A : Set) → Set
Paths A = Σ (A × A) (λ p → p1 p ≡ p2 p)

contr-Paths : {A : Set} → Paths A ≈ A
contr-Paths {A} = (λ pa → p1 (p1 pa)) 
                , (λ x → (x , x) , refl) 
                , (λ x → refl) 
                , (λ { ((a₁ , .a₁) , refl) → refl })

Homotopies : Set → Set → Set
Homotopies A B = Σ ((A → B) × (A → B)) (λ fg → (x : A) → p1 fg x ≡ p2 fg x)

{-
  Proof is postponed for now. It is already a well estabilished proof
  from the univalence axiom, anyway. :-)
-}

postulate
  fun-ext : ∀{a b}{A : Set a}{B : Set b}{f g : A → B}
          → (∀ x → f x ≡ g x)
          → f ≡ g
