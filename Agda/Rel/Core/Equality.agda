module Rel.Core.Equality where

open import Relation.Binary.PropositionalEquality
open import Data.Product using (_×_; ∃; _,_; uncurry; proj₁; proj₂)
open import Rel.Core hiding (p1; p2)
open import Function using (id; flip)

open import Rel.Core.HOTT using (fun-ext)

-- We can define relational equality in terms of inclusion.
infix 6 _≡r_
record _≡r_ {A B : Set}(R S : Rel A B) : Set where
  constructor _,_
  field
    p1 : R ⊆ S
    p2 : S ⊆ R

≡r-refl : {A B : Set}{R : Rel A B}
        → R ≡r R
≡r-refl = ⊆-refl , ⊆-refl

≡r-sym : {A B : Set}{R S : Rel A B}
       → R ≡r S → S ≡r R
≡r-sym h = _≡r_.p2 h , _≡r_.p1 h

≡r-trans : {A B : Set}{R S T : Rel A B}
         → R ≡r S → S ≡r T → R ≡r T
≡r-trans rs st = ⊆-trans (_≡r_.p1 rs) (_≡r_.p1 st) , ⊆-trans (_≡r_.p2 st) (_≡r_.p2 rs)

-- And some syntax sugar:

-- Left elimination
≡r-elim1 : {A B : Set}{R S : Rel A B}
      → R ≡r S → R ⊆ S
≡r-elim1 = _≡r_.p1

-- Right elimination
≡r-elim2 : {A B : Set}{R S : Rel A B}
      → R ≡r S → S ⊆ R
≡r-elim2 = _≡r_.p2

-- introduction
≡r-intro : {A B : Set}{R S : Rel A B}
      → R ⊆ S → S ⊆ R → R ≡r S
≡r-intro p1 p2 = p1 , p2

---------------------------------------------------------------
-- Relation Extensionality

-- This should NOT be used if you want your model verified. Check
-- the core module for anti-symmetry of ⊆. 
≡r-promote : {A B : Set}{R S : Rel A B}
             → R ≡r S → R ≡ S
≡r-promote {R = R} {S = S} (⊆in rs , ⊆in sr)
  = Λ-ext (λ a → ℙ-ext (flip R a) (flip S a) (rs a) (sr a))
  where
    -- power transpose
    Λ_ : {A B : Set}(R : Rel A B) → A → ℙ B
    Λ R = λ a b → R b a 

    Λ-ext : {A B : Set}{R S : Rel A B}
            → (∀ a → (Λ R) a ≡ (Λ S) a)
            → R ≡ S
    Λ-ext {R = R} {S = S} prf with Λ R | Λ S
    ...| lR | lS = fun-ext (λ b → fun-ext (λ a → cong (λ f → f b) (prf a)))

    postulate
      -- Beeing the same set, however, is having the same elements.
      -- Since in our scenario, the set (r x) beeing inhabited only
      -- means that x is an element of r (with our encoding of sets).
      -- so, to prove equality, we can boil down to saying that
      -- it's enough for r and s to be inhabited at the same time.
      ℙ-ext : {A : Set}(s1 s2 : ℙ A)
            → (∀ x → s1 x → s2 x)
            → (∀ x → s2 x → s1 x)
            → s1 ≡ s2     

      -- note: this is some sort of cheap way out, though. In the end, since 
      --       I'm assuming traditional set equality to be part of Agda's equality,
      --       of course I'll be able to prove relational equality, which is
      --       set equality over pairs.

-- Substitution. 
--
≡r-subst : {A B : Set}(P : Rel A B → Set){R S : Rel A B} 
         → R ≡r S → P R → P S
≡r-subst p rs pr = subst p (≡r-promote rs) pr


-- Another option is to define relational equality using indirect equality.
--
-- As we would expect, this is also an equivalence relation.
infix 6 _≡i_
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

-----------------------------------------------------------------------
-- Equality Conversion

-- And we can easily convert between the two definitions!
≡-itor : {A B : Set}{R S : Rel A B}
       → R ≡i S → R ≡r S
≡-itor {R = R} {S = S} rs 
  = proj₂ (rs R) ⊆-refl
  , proj₁ (rs S) ⊆-refl

≡-rtoi : {A B : Set}{R S : Rel A B}
       → R ≡r S → R ≡i S
≡-rtoi {R = R} {S = S} rs
  = λ x → (λ xs → ⊆in (λ a b bXa → ⊆out (_≡r_.p2 rs) a b (⊆out xs a b bXa)))
        , (λ xs → ⊆in (λ a b bXa → ⊆out (_≡r_.p1 rs) a b (⊆out xs a b bXa)))

-- Just to complete the module, a promotion and substitution for _≡i_
≡i-promote : {A B : Set}{R S : Rel A B}
           → R ≡i S → R ≡ S
≡i-promote r≡is = ≡r-promote (≡-itor r≡is)

≡i-subst : {A B : Set}(P : Rel A B → Set){R S : Rel A B} 
         → R ≡i S → P R → P S
≡i-subst p rs pr = ≡r-subst p (≡-itor rs) pr
