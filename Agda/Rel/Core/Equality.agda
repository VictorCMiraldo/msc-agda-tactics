module Rel.Core.Equality where

open import Data.Product using (_×_; ∃; _,_) renaming (proj₁ to p1; proj₂ to p2)
open import Rel.Core.Core

-- We can define relational equality in terms of inclusion.
infix 6 _≡r_
_≡r_ : {A B : Set} → Rel A B → Rel A B → Set
R ≡r S = (R ⊆ S) × (S ⊆ R)

≡r-refl : {A B : Set}{R : Rel A B}
        → R ≡r R
≡r-refl = ⊆-refl , ⊆-refl

≡r-sym : {A B : Set}{R S : Rel A B}
       → R ≡r S → S ≡r R
≡r-sym h = p2 h , p1 h

≡r-trans : {A B : Set}{R S T : Rel A B}
         → R ≡r S → S ≡r T → R ≡r T
≡r-trans rs st = ⊆-trans (p1 rs) (p1 st) , ⊆-trans (p2 st) (p2 rs)

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
