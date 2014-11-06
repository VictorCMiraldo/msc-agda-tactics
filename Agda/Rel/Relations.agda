module Rel.Relations where

open import Relation.Binary.PropositionalEquality
open import Data.Product using (_×_; ∃; _,_) renaming (proj₁ to p1; proj₂ to p2)
open import Data.Sum using (_⊎_) renaming (inj₁ to i1; inj₂ to i2)
open import Function using (id; _∘_)

-- Mu, Ko and Jansson encoding.

-- A set (s : ℙ A) is a function mapping (a : A) to a type, which encodes 
-- a logic formula determining its membership.
ℙ : Set → Set1
ℙ A = A → Set

singleton : {A : Set} → A → ℙ A
singleton a = λ a' → a ≡ a'

_∪_ : {A : Set} → ℙ A → ℙ A → ℙ A
(r ∪ s) a = r a ⊎ s a

_∩_ : {A : Set} → ℙ A → ℙ A → ℙ A
(r ∩ s) a = r a × s a

_⊆_ : {A : Set} → ℙ A → ℙ A → Set
r ⊆ s = ∀ a → r a → s a

⊆-refl : {A : Set}{r : ℙ A} → r ⊆ r
⊆-refl = λ _ ra → ra

⊆-trans : {A : Set}{r s t : ℙ A}
        → r ⊆ s → s ⊆ t → r ⊆ t
⊆-trans rs st a ar = st a (rs a ar)

-- A relation can be represented as:
--    ℙ (A × B)
--  ≡ ℙ (B × A)
--  ≡ B × A → Set
--  ≡ B → A → Set
--
Rel : Set → Set → Set1
Rel A B = B → A → Set

-- Relation Inclusion
infix 6 _⊑_
_⊑_ : {A B : Set} → Rel A B → Rel A B → Set
R ⊑ S = ∀ b a → R b a → S b a

-- The converse of a relation.
_ᵒ : {A B : Set} → Rel A B → Rel B A
(R ᵒ) a b = R b a 

-- Relation composition
_∙_ : {A B C : Set} → Rel B C → Rel A B → Rel A C
(R ∙ S) c a = ∃ (λ b → (R c b) × (S b a))

fun : {A B : Set} → (A → B) → Rel A B
fun f b a = f a ≡ b

fun-comp : {A B C : Set} {f : B → C} {g : A → B}
         → fun (f ∘ g)  ⊑  fun f ∙ fun g
fun-comp {g = g} c a fga = g a , fga , refl

-- Identity Relation
Id : {A : Set} → Rel A A
Id = fun id

-- Relational Split
⟨_,_⟩ : {A B C : Set} → Rel A B → Rel A C → Rel A (B × C)
⟨ R , S ⟩ = λ bc a → (R (p1 bc) a) × (S (p2 bc) a)

-- Relational Constants
-- TODO: how to write those guys?
π₁ : {A B : Set} → Rel (A × B) A
π₁ a ab = fun p1 a ab

-- shouldn't π₁ return A as long as (a == p1 ab)?
-- what to do otherwise, then?

π₂ : {A B : Set} → Rel (A × B) B
π₂ b ab = fun p2 b ab

-- Relational product
_X_ : {A B C D : Set} → Rel A B → Rel C D → Rel (A × C) (B × D)
(R X S) bd ac = R (p1 bd) (p1 ac) × S (p2 bd) (p2 ac)

-- Product correct?
X-uni-left : ∀{A B C} → {X : Rel C (A × B)}
           → (R : Rel C A) 
           → (S : Rel C B) 
           → X ⊑ ⟨ R , S ⟩ 
           → ((π₁ ∙ X) ⊑ R) × ((π₂ ∙ X) ⊑ S)
X-uni-left r s prf = (λ a b → {!!}) , {!!}

-- Constructive encoding, using datas? 
