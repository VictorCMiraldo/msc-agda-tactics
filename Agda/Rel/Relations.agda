module Rel.Relations where

open import Data.Bool using (Bool; true; false)
open import Relation.Binary.PropositionalEquality
open import Data.Product using (_×_; ∃; _,_) renaming (proj₁ to p1; proj₂ to p2)
open import Data.Sum using (_⊎_; [_,_]) renaming (inj₁ to i1; inj₂ to i2; [_,_]′ to case)
open import Function using (id; _∘_)

--------------
-- * Sets * --
--------------

-- Mu, Ko and Jansson encoding.

-- A set (s : ℙ A) is a function mapping (a : A) to a type, which encodes 
-- a logic formula determining its membership.
--
-- Some other possibilities would be:
--   ℙ A = A → Bool, but this requires everything to be decidable, which may not be the case, take functions 
--                   with infinite domain, for instance. 
--
--   ℙ A = A → U, where U is a universe defined by us with the operations we'll support in our logic.
--                seems like a good shot.
--
-- Let's take a (s : ℙ A), if (x : A) ∈ s, then s x is mapped to ⊤,
-- s maps x to ⊥ otherwise.
ℙ : Set → Set1
ℙ A = A → Set

-- The singleton set, for instance, has type A → ℙ A.
-- Expanding it we get (x : A) → (y : A) → Set.
-- Hence, we want to return a set that is populated when
-- y ∈ { x }. Well, that happens when x ≡ y.
singleton : {A : Set} → A → ℙ A
singleton a = λ a' → a ≡ a'

-- Set-theoretic operations can also be defined easily.

-- Union
_∪_ : {A : Set} → ℙ A → ℙ A → ℙ A
(r ∪ s) a = r a ⊎ s a

-- Intersection
_∩_ : {A : Set} → ℙ A → ℙ A → ℙ A
(r ∩ s) a = r a × s a

-- Subset relation
_⊆s_ : {A : Set} → ℙ A → ℙ A → Set
r ⊆s s = ∀ a → r a → s a

-- Subset is reflexive
⊆s-refl : {A : Set}{r : ℙ A} → r ⊆s r
⊆s-refl = λ _ ra → ra

-- Subset is transitive
⊆s-trans : {A : Set}{r s t : ℙ A}
        → r ⊆s s → s ⊆s t → r ⊆s t
⊆s-trans rs st a ar = st a (rs a ar)

-------------------
-- * Relations * --
-------------------

-- A relation can be represented as:
--    ℙ (A × B)
--  ≡ ℙ (B × A)
--  ≡ B × A → Set
--  ≡ B → A → Set
--
-- Note that the arguments are in reverse order.
Rel : Set → Set → Set1
Rel A B = B → A → Set

-- Relational Inclusion
-- Whenever R ⊆ S, it means that ∀a b . a R b ⇒ a S b
infix 6 _⊆_
_⊆_ : {A B : Set} → Rel A B → Rel A B → Set
R ⊆ S = ∀ b a → R b a → S b a

------------------------------
-- * Inclusion Properties * --
------------------------------

-- We can define relational equality in terms of inclusion.
infix 6 _≡r_
_≡r_ : {A B : Set} → Rel A B → Rel A B → Set
R ≡r S = (R ⊆ S) × (S ⊆ R)

-- And some syntax sugar:

-- Left elimination
≡r-elim1 : {A B : Set}{R S : Rel A B}
      → R ≡r S → R ⊆ S
≡r-elim1 = p1

-- Right elimination
≡r-elim2 : {A B : Set}{R S : Rel A B}
      → R ≡r S → S ⊆ R
≡r-elim2 = p2

-- introduction
≡r-intro : {A B : Set}{R S : Rel A B}
      → R ⊆ S → S ⊆ R → R ≡r S
≡r-intro p1 p2 = p1 , p2

------------------
-- * Converse * --
------------------

-- The converse of a relation.
_ᵒ : {A B : Set} → Rel A B → Rel B A
(R ᵒ) a b = R b a 

-- Relational composition is given in terms of a existential quantifier,
-- which, in turn, is a relational poduct.
-- The type of (R ∙ S) then, is a pair where the first element
-- is a witness of the composition, of type B, and the second
-- is a pair of proofs, that b is indeed a 'bridge' for the composition.
infixr 10 _∙_
_∙_ : {A B C : Set} → Rel B C → Rel A B → Rel A C
(R ∙ S) c a = ∃ (λ b → (R c b) × (S b a))

-- Lifting a function to a relation is pretty simple
fun : {A B : Set} → (A → B) → Rel A B
fun f b a = f a ≡ b

-- We can prove that function composition distributes over functional lifting.
fun-comp : {A B C : Set} {f : B → C} {g : A → B}
         → fun (f ∘ g)  ⊆  fun f ∙ fun g
fun-comp {g = g} c a fga = g a , fga , refl

-- Identity Relation
Id : {A : Set} → Rel A A
Id = fun id

--------------------
-- ** Products ** --
--------------------

-- Relational Constants
π₁ : {A B : Set} → Rel (A × B) A
π₁ a ab = fun p1 a ab

π₂ : {A B : Set} → Rel (A × B) B
π₂ b ab = fun p2 b ab

-- Relational Split
⟨_,_⟩ : {A B C : Set} → Rel A B → Rel A C → Rel A (B × C)
⟨ R , S ⟩ = λ bc a → (R (p1 bc) a) × (S (p2 bc) a)

-- Relational product
_*_ : {A B C D : Set} → Rel A B → Rel C D → Rel (A × C) (B × D)
(R * S) bd ac = R (p1 bd) (p1 ac) × S (p2 bd) (p2 ac)

----
---- Product Universsal Property:
----
----   X ⊆ ⟨ R ; S ⟩ ≡ (π₁ ∙ X) ⊆ R ∧ (π₂ ∙ X) ⊆ S 
----

prod-uni-r1 : ∀{A B C} → {X : Rel C (A × B)}
             → (R : Rel C A) → (S : Rel C B)
             → X ⊆ ⟨ R , S ⟩
             → π₁ ∙ X ⊆ R
prod-uni-r1 {X = X} r s prf
  = λ a c hip →
    let wita , witb  = p1 hip -- the pair witnessing the composition. 
        aπ₁ab , abXc = p2 hip
        k = pair-lemma-l (p1 hip) a aπ₁ab
    in p1 (prf (a , witb) c (subst (λ x → X x c) k abXc))
  where
    pair-lemma-l : {A B : Set} → (h : A × B) → (x : A) → p1 h ≡ x → h ≡ (x , p2 h)
    pair-lemma-l h .(p1 h) refl = refl

prod-uni-r2 : ∀{A B C} → {X : Rel C (A × B)}
            → (R : Rel C A) → (S : Rel C B)
            → X ⊆ ⟨ R , S ⟩
            → π₂ ∙ X ⊆ S
prod-uni-r2 {X = X} r s prf
  = λ b c hip → 
    let wita , witb  = p1 hip 
        bπ₂ab , abXc = p2 hip
        k = pair-lemma-r (p1 hip) b bπ₂ab
    in p2 (prf (wita , b) c (subst (λ x → X x c) k abXc))
  where
    pair-lemma-r : {A B : Set} → (h : A × B) → (x : B) → p2 h ≡ x → h ≡ (p1 h , x)
    pair-lemma-r h .(p2 h) refl = refl

prod-uni-l : ∀{A B C} → {X : Rel C (A × B)}
           → (R : Rel C A) → (S : Rel C B)
           → (π₁ ∙ X) ⊆ R → (π₂ ∙ X) ⊆ S
           → X ⊆ ⟨ R , S ⟩
prod-uni-l {X = X} r s pr ps 
  = λ ab c hip →
    let a , b = ab
    in pr a c (ab , refl , hip) , ps b c (ab , refl , hip)


----------------------
-- ** Coproducts ** --
----------------------

-- Either
either : {A B C : Set} → (R : Rel A C) → (S : Rel B C) → Rel (A ⊎ B) C
either R S c ab = case (R c) (S c) ab

-- Coproduct constants
ι₁ : {A B : Set} → Rel A (A ⊎ B)
ι₁ = fun i1

ι₂ : {A B : Set} → Rel B (A ⊎ B)
ι₂ = fun i2

-- Sum
_+_ : {A B C D : Set} → (R : Rel A B) → (S : Rel C D) → Rel (A ⊎ C) (B ⊎ D)
R + S = either (ι₁ ∙ R) (ι₂ ∙ S)

------------------
-- Coproduct Universal

coprod-uni-r1 : ∀{A B C}{X : Rel (A ⊎ B) C}
              → (R : Rel A C) → (S : Rel B C)
              → (X ≡r either R S) 
              → R ≡r X ∙ ι₁
coprod-uni-r1 {X = X} r s prf
  = (λ c a hip → i1 a , ≡r-elim2 prf c (i1 a) hip , refl) 
  , (λ c a hip → let wit , hprf = hip
                 in ≡r-elim1 prf c (i1 a) (subst (X c) (sym (p2 hprf)) (p1 hprf)))

coprod-uni-r2 : ∀{A B C}{X : Rel (A ⊎ B) C}
              → (R : Rel A C) → (S : Rel B C)
              → (X ≡r either R S) 
              → S ≡r X ∙ ι₂
coprod-uni-r2 {X = X} r s prf
  = (λ c b hip → i2 b , ≡r-elim2 prf c (i2 b) hip , refl)
  , (λ c b hip → let wit , hprf = hip 
                 in ≡r-elim1 prf c (i2 b) (subst (X c) (sym (p2 hprf)) (p1 hprf)))

-- The left proof will be provided by two auxiliary proofs, since it is a big one.
--
-- Left implication
--
coprod-uni-l-aux1 : ∀{A B C}{X : Rel (A ⊎ B) C}
                  → (R : Rel A C) → (S : Rel B C)
                  → (R ≡r X ∙ ι₁) → (S ≡r X ∙ ι₂)
                  → X ⊆ either R S
coprod-uni-l-aux1  {X = X} r s pr ps
  = λ { c (i1 a) hip → (≡r-elim2 pr) c a (coprod-lemma-i1 {X = X} a c hip)
      ; c (i2 b) hip → (≡r-elim2 ps) c b (coprod-lemma-i2 {X = X} b c hip)
      }
  where
    coprod-lemma-i1 : ∀{A B C}{X : Rel (A ⊎ B) C}
                    → (a : A) → (c : C)
                    → X c (i1 a) 
                    → (X ∙ ι₁) c a
    coprod-lemma-i1 a c cXi1a = i1 a , cXi1a , refl 

    coprod-lemma-i2 : ∀{A B C}{X : Rel (A ⊎ B) C}
                    → (b : B) → (c : C)
                    → X c (i2 b) 
                    → (X ∙ ι₂) c b
    coprod-lemma-i2 b c cXi2b = i2 b , cXi2b , refl

-- Right implication
--
coprod-uni-l-aux2 : ∀{A B C}{X : Rel (A ⊎ B) C}
                  → (R : Rel A C) → (S : Rel B C)
                  → (R ≡r X ∙ ι₁) → (S ≡r X ∙ ι₂)
                  → either R S ⊆ X
coprod-uni-l-aux2 {X = X} r s pr ps
  = λ { c (i1 a) hip → let aux = ≡r-elim1 pr c a hip
                       in subst (X c) (sym (p2 (p2 aux))) (p1 (p2 aux))
      ; c (i2 b) hip → let aux = ≡r-elim1 ps c b hip
                       in subst (X c) (sym (p2 (p2 aux))) (p1 (p2 aux))
      }

-- And, finally, the universal.
coprod-uni-l : ∀{A B C}{X : Rel (A ⊎ B) C}
             → (R : Rel A C) → (S : Rel B C)
             → (R ≡r X ∙ ι₁) → (S ≡r X ∙ ι₂)
             → X ≡r either R S
coprod-uni-l r s pr ps = ≡r-intro (coprod-uni-l-aux1 r s pr ps) (coprod-uni-l-aux2 r s pr ps)
