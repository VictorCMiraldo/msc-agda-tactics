module Rel.Core.Product where

open import Data.Product using (_×_; ∃; _,_) renaming (proj₁ to p1; proj₂ to p2)
open import Relation.Binary.PropositionalEquality
open import Rel.Core.Core

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
prod-uni-r1 {X = X} r s (⊆in prf)
  = ⊆in (λ c a hip →
         let wita , witb  = p1 hip -- the pair witnessing the composition. 
             aπ₁ab , abXc = p2 hip
             k = pair-lemma-l (p1 hip) a aπ₁ab
         in p1 (prf c (a , witb) (subst (λ x → X x c) k abXc))
  ) where
    pair-lemma-l : {A B : Set} → (h : A × B) → (x : A) → p1 h ≡ x → h ≡ (x , p2 h)
    pair-lemma-l h .(p1 h) refl = refl


prod-uni-r2 : ∀{A B C} → {X : Rel C (A × B)}
            → (R : Rel C A) → (S : Rel C B)
            → X ⊆ ⟨ R , S ⟩
            → π₂ ∙ X ⊆ S
prod-uni-r2 {X = X} r s (⊆in prf)
  = ⊆in (λ c b hip → 
         let wita , witb  = p1 hip 
             bπ₂ab , abXc = p2 hip
             k = pair-lemma-r (p1 hip) b bπ₂ab
         in p2 (prf c (wita , b) (subst (λ x → X x c) k abXc))
  ) where
    pair-lemma-r : {A B : Set} → (h : A × B) → (x : B) → p2 h ≡ x → h ≡ (p1 h , x)
    pair-lemma-r h .(p2 h) refl = refl


prod-uni-l : ∀{A B C} → {X : Rel C (A × B)}
           → (R : Rel C A) → (S : Rel C B)
           → (π₁ ∙ X) ⊆ R → (π₂ ∙ X) ⊆ S
           → X ⊆ ⟨ R , S ⟩
prod-uni-l {X = X} r s pr ps 
  = ⊆in (λ c ab hip →
         let a , b = ab
         in (⊆out pr) c a (ab , refl , hip) , (⊆out ps) c b (ab , refl , hip))
