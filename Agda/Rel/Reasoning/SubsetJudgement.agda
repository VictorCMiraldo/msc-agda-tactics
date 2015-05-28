module Rel.Reasoning.SubsetJudgement where

  open import Data.Product using (_×_; ∃; _,_) renaming (proj₁ to p1; proj₂ to p2)
  open import Function using (id; _∘_)

  open import Data.Unit using (Unit; unit)
  open import Data.Empty using (⊥; ⊥-elim)

  open import Rel.Core renaming (Rel to R)
  open import Rel.Core.Equality
  open import Relation.Binary
  open import Level using (Level; zero; suc; _⊔_)

  ------------------------------------
  -- * Preorder Declarations

  _⇐_ : ∀{a b} → Set a → Set b → Set (a ⊔ b)
  P ⇐ Q = Q → P

  ⇐-refl : ∀{a}{P : Set a} → P ⇐ P
  ⇐-refl = id

  ⇐-trans : ∀{a}{P Q R : Set a} → P ⇐ Q → Q ⇐ R → P ⇐ R
  ⇐-trans pq qr = pq ∘ qr 

  _⇔_ : ∀{a b} → Set a → Set b → Set (a ⊔ b)
  p ⇔ q = (p ⇐ q) × (q ⇐ p)

  ⇔-refl : ∀{a}{P : Set a} → P ⇔ P
  ⇔-refl = ⇐-refl , ⇐-refl

  ⇔-sym : ∀{a}{P Q : Set a} → P ⇔ Q → Q ⇔ P
  ⇔-sym ( pq , qp ) = qp , pq

  ⇔-trans : ∀{a}{P Q R : Set a} → P ⇔ Q → Q ⇔ R → P ⇔ R
  ⇔-trans (pq , qp) (qr , rq) = ⇐-trans pq qr , ⇐-trans rq qp

  ----------------------------------
  -- Structure Declarations

  ⇔-IsEquivalence : ∀{a} → IsEquivalence (_⇔_ {a = a})
  ⇔-IsEquivalence = record
    { refl  = ⇔-refl
    ; sym   = ⇔-sym
    ; trans = ⇔-trans
    }

  ⇐-IsPreorder : ∀{a} → IsPreorder (_⇔_ {a = a}) (_⇐_ {a = a})
  ⇐-IsPreorder = record
    { isEquivalence = ⇔-IsEquivalence
    ; reflexive     = p1
    ; trans         = ⇐-trans
    }

  ⇐-Preorder : ∀{a} → Preorder (suc a) a a
  ⇐-Preorder {a} = record
    { Carrier = Set a
    ; _≈_     = _⇔_
    ; _∼_     = _⇐_
    ; isPreorder = ⇐-IsPreorder {a}
    }

  module ⊆-Reasoning {a} where
    import Relation.Binary.PreorderReasoning {suc a} {p₂ = a} as Pre
    open Pre ⇐-Preorder public 
      renaming ( _∼⟨_⟩_ to _⇐⟨_⟩_
               ; _≈⟨_⟩_ to _⇔⟨_⟩_
               )

    tautology : (A : Set a) → Set a
    tautology A = A ⇐ Unit

  -- Some substitution lemmas to ease the handling of a single
  -- side of our inclusion
  subst-r : {A B : Set}{R S S' : R A B}
          → S' ≡r S → R ⊆ S → R ⊆ S'
  subst-r (_ , ss') rs = ⊆-trans rs ss' 


  subst-l : {A B : Set}{R R' S : R A B}
          → R' ≡r R → R ⊆ S → R' ⊆ S
  subst-l (r'r , _) rs = ⊆-trans r'r rs
