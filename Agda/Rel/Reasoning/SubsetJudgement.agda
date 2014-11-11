module Rel.Reasoning.SubsetJudgement where

open import Data.Product using (_×_; ∃; _,_) renaming (proj₁ to p1; proj₂ to p2)
open import Function using (id; _∘_)

open import Data.Unit using (Unit; unit)
open import Data.Empty using (⊥; ⊥-elim)

open import Rel.Core.Core renaming (Rel to R)
open import Rel.Core.Equality
open import Relation.Binary
open import Level using (Level; zero; suc)

------------------------------------
-- * Preorder Declarations

_⇐_ : Set → Set → Set
P ⇐ Q = Q → P

⇐-refl : {P : Set} → P ⇐ P
⇐-refl = id

⇐-trans : {P Q R : Set} → P ⇐ Q → Q ⇐ R → P ⇐ R
⇐-trans pq qr = pq ∘ qr 

_⇔_ : Set → Set → Set
p ⇔ q = (p ⇐ q) × (q ⇐ p)

⇔-refl : {P : Set} → P ⇔ P
⇔-refl = ⇐-refl , ⇐-refl

⇔-sym : {P Q : Set} → P ⇔ Q → Q ⇔ P
⇔-sym ( pq , qp ) = qp , pq

⇔-trans : {P Q R : Set} → P ⇔ Q → Q ⇔ R → P ⇔ R
⇔-trans (pq , qp) (qr , rq) = ⇐-trans pq qr , ⇐-trans rq qp

----------------------------------
-- Structure Declarations

⇔-IsEquivalence : IsEquivalence _⇔_
⇔-IsEquivalence = record
  { refl  = ⇔-refl
  ; sym   = ⇔-sym
  ; trans = ⇔-trans
  }

⇐-IsPreorder : IsPreorder _⇔_ _⇐_
⇐-IsPreorder = record
  { isEquivalence = ⇔-IsEquivalence
  ; reflexive     = p1
  ; trans         = ⇐-trans
  }

⇐-Preorder : Preorder _ _ _
⇐-Preorder = record
  { Carrier = Set
  ; _≈_     = _⇔_
  ; _∼_     = _⇐_
  ; isPreorder = ⇐-IsPreorder
  }

import Relation.Binary.PreorderReasoning as Pre
open Pre ⇐-Preorder public renaming (_∼⟨_⟩_ to _≡⟨_⟩_)

-- Some substitution lemmas to ease the handling of a single
-- side of our inclusion
subst-r : {A B : Set}{R S S' : R A B}
        → S' ≡r S → R ⊆ S → R ⊆ S'
subst-r (_ , ss') rs b a bRa = ss' b a (rs b a bRa)


subst-l : {A B : Set}{R R' S : R A B}
        → R' ≡r R → R ⊆ S → R' ⊆ S
subst-l (r'r , _) rs b a bR'a = rs b a (r'r b a bR'a)
