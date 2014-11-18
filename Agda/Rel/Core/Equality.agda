module Rel.Core.Equality where

open import Relation.Binary.PropositionalEquality
open import Data.Product using (_×_; ∃; _,_) renaming (proj₁ to p1; proj₂ to p2)
open import Rel.Core.Core
open import Function using (id)

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

-- Substitution. 
-- 
-- This is tricky. I believe that I can safely add the ≡r-promote postulate
-- since once I have a proof that relations R and S are the same relation,
-- I can argue that they'll eventually reduce to the same value.
--
-- It is hard to prove R ≡r S → R ≡ S direcly mostly because of
-- extensionality. 
--
-- We chose to leave this postulate hidden from the user, so, to work
-- with relations he only needs Rel.Core.Equality and no equality from
-- the standard library.
≡r-subst : {A B : Set}(P : Rel A B → Set){R S : Rel A B} 
         → R ≡r S → P R → P S
≡r-subst p rs pr = subst p (≡r-promote rs) pr
  where 
    postulate
      ≡r-promote : {A B : Set}{R S : Rel A B} → R ≡r S → R ≡ S


-- Another option is to define relational equality using indirect equality.
--
-- As we would expect, this is also an equivalence relation.
_≡i_ : {A B : Set} → Rel A B → Rel A B → Set1
r ≡i s = ∀ x → (x ⊆ s → x ⊆ r) × (x ⊆ r → x ⊆ s)

≡i-refl : {A B : Set}{R : Rel A B} → R ≡i R
≡i-refl _ = id , id

≡i-sym : {A B : Set}{R S : Rel A B} → R ≡i S → S ≡i R
≡i-sym r≡is x = let xsxr , xrxs = r≡is x
                in xrxs , xsxr

≡i-trans : {A B : Set}{R S T : Rel A B}
         → R ≡i S → S ≡i T → R ≡i T
≡i-trans rs st x 
  = let xtxs , xsxt = st x
        xsxr , xrxs = rs x
    in (λ xt → xsxr (xtxs xt)) 
     , (λ xr → xsxt (xrxs xr))

-- And we can easily convert between the two definitions!
≡-itor : {A B : Set}{R S : Rel A B}
       → R ≡i S → R ≡r S
≡-itor {R = R} {S = S} rs 
  = p2 (rs R) ⊆-refl 
  , p1 (rs S) ⊆-refl


≡-rtoi : {A B : Set}{R S : Rel A B}
       → R ≡r S → R ≡i S
≡-rtoi {R = R} {S = S} rs
  = λ x → (λ xs → ⊆in (λ a b bXa → ⊆out (p2 rs) a b (⊆out xs a b bXa)))
        , (λ xs → ⊆in (λ a b bXa → ⊆out (p1 rs) a b (⊆out xs a b bXa)))

-- Just to complete the module, a substitution for _≡i_
≡i-subst : {A B : Set}(P : Rel A B → Set){R S : Rel A B} 
         → R ≡i S → P R → P S
≡i-subst p rs pr = ≡r-subst p (≡-itor rs) pr
