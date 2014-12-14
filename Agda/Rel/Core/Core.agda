module Rel.Core.Core where

open import Data.Bool using (Bool; true; false)
open import Relation.Binary.PropositionalEquality
open import Data.Product using (Σ; _×_; ∃; _,_; uncurry′; curry) renaming (proj₁ to p1; proj₂ to p2)
open import Data.Sum using (_⊎_; [_,_]) renaming (inj₁ to i1; inj₂ to i2; [_,_]′ to case)
open import Function using (id; _∘_)

open import Data.Unit using (Unit; unit)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.Core hiding (Rel)
open import Relation.Nullary.Core
open import Relation.Nullary.Decidable

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

-- A relation can be represented as:
--    ℙ (A × B)
--  ≡ ℙ (B × A)
--  ≡ B × A → Set
--  ≡ B → A → Set
--
-- Note that the arguments are in reverse order.
Rel : Set → Set → Set1
Rel A B = B → A → Set  

-- Now we need some Homotopy Type Theory Machinery:
open import Rel.Core.HOTT

-- Relational extensionality written as curried function extensionality.
rel-ext : {A B : Set}{R S : Rel A B}
        → (∀ b a → R b a ≡ S b a)
        → R ≡ S
rel-ext {R = R} {S = S} prf 
  = uncurry-inj (fun-ext {f = uncurry′ R} {g = uncurry′ S} 
                 (λ x → prf (p1 x) (p2 x)))
  where
    uncurry-inj : ∀{a b c}{A : Set a}{B : Set b}{C : Set c}{f g : A → B → C}
                → uncurry′ f ≡ uncurry′ g → f ≡ g
    uncurry-inj prf = cong curry prf

----------------------
-- * Type Classes * --
----------------------

record IsProp {A B : Set}(R : Rel A B) : Set where
  constructor mp
  field isprop : ∀ b a → isProp (R b a) 

record IsDec {A B : Set}(R : Rel A B) : Set where
  constructor dec
  field undec : Decidable R
    
open IsDec {{...}}
open IsProp {{...}}

--------------
-- * Sets * --
--------------

-- The singleton set, for instance, has type A → ℙ A.
-- Expanding it we get (x : A) → (y : A) → Set.
-- Hence, we want to return a set that is populated when
-- y ∈ { x }. Well, that happens when x ≡ y.
singleton : {A : Set} → A → ℙ A
singleton a = λ a' → a ≡ a'

-- Set-theoretic operations can also be defined easily.

-- Union
_∪s_ : {A : Set} → ℙ A → ℙ A → ℙ A
(r ∪s s) a = r a ⊎ s a

-- Intersection
_∩s_ : {A : Set} → ℙ A → ℙ A → ℙ A
(r ∩s s) a = r a × s a

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

----------------------------
-- * Relation Inclusion * --
----------------------------

-- Relational Inclusion
-- Whenever R ⊆ S, it means that ∀a b . a R b ⇒ a S b
infix 6 _⊆_
data _⊆_ {A B : Set}(R S : Rel A B) : Set where
  ⊆in : (∀ a b → R b a → S b a) → R ⊆ S

⊆out : {A B : Set}{R S : Rel A B}
     → R ⊆ S → (∀ a b → R b a → S b a)
⊆out (⊆in f) = f

-- Inclusion is reflexive
⊆-refl : {A B : Set}{R : Rel A B} → R ⊆ R
⊆-refl = ⊆in (λ _ _ → id)

-- And transitive
⊆-trans : {A B : Set}{R S T : Rel A B}
        → R ⊆ S → S ⊆ T → R ⊆ T
⊆-trans (⊆in rs) (⊆in st) 
  = ⊆in (λ a b bRa → st a b (rs a b bRa))

-- Anti-Symmetry is a tricky proof. Is the user really wants to be formal,
-- he needs to prove his relations are decidable and mere propositions.
-- That would be a good call for realeasing code; Yet, for testing purposes
-- only, check the module Rel.Equality for ≡r-promote for a cheap way (with
-- some postulate black magic in the middle) to convert ≡r to ≡. 
⊆-antisym : {A B : Set}{R S : Rel A B} 
            ⦃ decr : IsDec R  ⦄ ⦃ decs : IsDec S ⦄
            ⦃ prpr : IsProp R ⦄ ⦃ prps : IsProp S ⦄
          → R ⊆ S → S ⊆ R → R ≡ S
⊆-antisym {R = R} {S = S} ⦃ dec dr ⦄ ⦃ dec ds ⦄ ⦃ mp pir ⦄ ⦃ mp pis ⦄ (⊆in rs) (⊆in sr)
  = rel-ext (λ b a 
  → let
      propS = pis b a
      propR = pir b a
    in case-analisys {R = R} {S = S} b a (rs a b) (sr a b) propR propS (dr b a) (ds b a))
  where
    case-analisys : {A B : Set}{R S : Rel A B}
                  → (b : B)(a : A)
                  → (R b a → S b a)
                  → (S b a → R b a)
                  → isProp (R b a)
                  → isProp (S b a)
                  → Dec (R b a) → Dec (S b a)
                  → R b a ≡ S b a
    case-analisys b a rs sr pr ps (yes bRa)  (yes bSa)  
      with ≈-to-≡ (lemma-332 pr bRa) | ≈-to-≡ (lemma-332 ps bSa)
    ...| ur | us = trans ur (sym us)
    case-analisys b a rs sr pr ps (yes bRa) (no ¬bSa) = ⊥-elim (¬bSa (rs bRa))
    case-analisys b a rs sr pr ps (no ¬bRa) (yes bSa) = ⊥-elim (¬bRa (sr bSa))
    case-analisys b a rs sr pr ps (no ¬bRa) (no ¬bSa) 
      with ≈-to-≡ (¬lemma-332 pr ¬bRa) | ≈-to-≡ (¬lemma-332 ps ¬bSa)
    ...| ur | us = trans ur (sym us)

-------------------------
-- * Other Operators * --
-------------------------

-- Relational Union
infix 8 _∪_
record _∪_ {A B : Set}(R S : Rel A B)(b : B)(a : A) : Set
  where constructor cons-∪
        field un : R b a ⊎ S b a

i1∪ : {A B : Set}{R S : Rel A B}{b : B}{a : A} → R b a → (R ∪ S) b a
i1∪ rba = cons-∪ (i1 rba)

i2∪ : {A B : Set}{R S : Rel A B}{b : B}{a : A} → S b a → (R ∪ S) b a
i2∪ sba = cons-∪ (i2 sba)

-- Relational Intersection
infix 8 _∩_
record _∩_ {A B : Set}(R S : Rel A B)(b : B)(a : A) : Set
  where constructor cons-∩
        field un : R b a × S b a

p1∩ : {A B : Set}{R S : Rel A B}{b : B}{a : A} → (R ∩ S) b a → R b a
p1∩ (cons-∩ (bRa , _)) = bRa

p2∩ : {A B : Set}{R S : Rel A B}{b : B}{a : A} → (R ∩ S) b a → S b a
p2∩ (cons-∩ (_ , bSa)) = bSa

-- Union universal
∪-uni-l : {A B : Set}(X R S : Rel A B)
        → R ∪ S ⊆ X 
        → (R ⊆ X) × (S ⊆ X)
∪-uni-l x r s (⊆in hip) 
        = ⊆in (λ b a bRa → hip b a (i1∪ bRa)) 
        , ⊆in (λ b a bSa → hip b a (i2∪ bSa)) 

∪-uni-r : {A B : Set}(X R S : Rel A B)
        → (R ⊆ X) × (S ⊆ X)
        → R ∪ S ⊆ X
∪-uni-r x r s hip 
        = ⊆in λ { b a (cons-∪ (i1 bRa)) → ⊆out (p1 hip) b a bRa
                ; b a (cons-∪ (i2 bSa)) → ⊆out (p2 hip) b a bSa
                }

-- Intersection Universal
∩-uni-l : {A B : Set}(X R S : Rel A B)
        → X ⊆ R ∩ S
        → (X ⊆ R) × (X ⊆ S)
∩-uni-l x r s (⊆in hip) 
        = ⊆in (λ b a bXa → p1∩ (hip b a bXa))
        , ⊆in (λ b a bXa → p2∩ (hip b a bXa))

∩-uni-r : {A B : Set}(X R S : Rel A B)
        → (X ⊆ R) × (X ⊆ S)
        → X ⊆ R ∩ S
∩-uni-r x r s (x⊆r , x⊆s) 
  = ⊆in (λ b a bXa → cons-∩ ((⊆out x⊆r) b a bXa , (⊆out x⊆s) b a bXa))

---------------------
-- * Composition * --
---------------------

-- Relational composition is given in terms of a existential quantifier,
-- which, in turn, is a relational poduct.
-- The type of (R ∙ S) then, is a pair where the first element
-- is a witness of the composition, of type B, and the second
-- is a pair of proofs, that b is indeed a 'bridge' for the composition.
infixr 10 _∙_
record _∙_ {A B C : Set}(R : Rel B C)(S : Rel A B)(c : C)(a : A) : Set
  where
    constructor _,_
    field
      witness  : B
      composes : (R c witness) × (S witness a)

p1∙ : {A B C : Set}{R : Rel B C}{S : Rel A B}{c : C}{a : A} → (R ∙ S) c a → B
p1∙ rs = _∙_.witness rs

p2∙ : {A B C : Set}{R : Rel B C}{S : Rel A B}{c : C}{a : A}(prf : (R ∙ S) c a) → (R c (p1∙ prf)) × (S (p1∙ prf) a)
p2∙ rs = _∙_.composes rs

--------------------------
-- * Function Lifting * --
--------------------------

-- Lifting a function to a relation is pretty simple
record fun {A B : Set}(f : A → B)(b : B)(a : A) : Set
  where constructor cons-fun
        field un : f a ≡ b

-- We can prove that function composition distributes over functional lifting.
fun-comp : {A B C : Set} {f : B → C} {g : A → B}
         → fun (f ∘ g)  ⊆  fun f ∙ fun g
fun-comp {g = g} = ⊆in (λ { a _ (cons-fun fga) → g a , cons-fun fga , cons-fun refl } )

-------------------
-- * Constants * --
-------------------

-- Identity Relation
Id : {A : Set} → Rel A A
Id = fun id

-- Top relation
Top : {A B : Set} → Rel A B
Top _ _ = Unit

-- Bottom relation
Bot : {A B : Set} → Rel A B
Bot _ _ = ⊥

------------------
-- * Converse * --
------------------

-- The converse of a relation.
_ᵒ : {A B : Set} → Rel A B → Rel B A
(R ᵒ) a b = R b a 

--------------------------
-- * Kernel and Image * --
--------------------------

ker : {A B : Set} → Rel A B → Rel A A
ker r = r ᵒ ∙ r

img : {A B : Set} → Rel A B → Rel B B
img r = r ∙ r ᵒ

-- Domain
δ : {A B : Set} → Rel A B → Rel A A
δ r = ker r ∩ Id

-- Image
ρ : {A B : Set} → Rel A B → Rel B B
ρ r = img r ∩ Id

