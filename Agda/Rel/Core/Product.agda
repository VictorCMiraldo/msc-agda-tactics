module Rel.Core.Product where

open import Data.Product using (_×_; ∃; _,_) renaming (proj₁ to p1; proj₂ to p2)
open import Relation.Binary.PropositionalEquality
open import Rel.Core.Core
open import Rel.Core.HOTT using (isProp)
open import Rel.Core.Equality

--------------------
-- ** Products ** --
--------------------

-- Relational Constants
π₁ : {A B : Set} → Rel (A × B) A
π₁ a ab = fun p1 a ab

π₂ : {A B : Set} → Rel (A × B) B
π₂ b ab = fun p2 b ab

-- Relational Split
record ⟨_,_⟩ {A B C : Set}(R : Rel A B)(S : Rel A C)(bc : B × C)(a : A) : Set
  where constructor cons-⟨,⟩
        field un : (R (p1 bc) a) × (S (p2 bc) a)

instance
  ⟨,⟩-isProp : {A B C : Set}{R : Rel A B}{S : Rel A C}
             → {{ prpR : IsProp R }} {{ prpS : IsProp S }}
             → IsProp ⟨ R , S ⟩
  ⟨,⟩-isProp ⦃ mp pR ⦄ ⦃ mp pS ⦄ 
    = mp (λ { (b , c) a → prop b c a (pR b a) (pS c a)})
    where
      prop : {A B C : Set}{R : Rel A B}{S : Rel A C}
           → (b : B)(c : C)(a : A) → isProp (R b a) → isProp (S c a)
           → isProp (⟨ R , S ⟩ (b , c) a)
      prop b c a bRa cSa (cons-⟨,⟩ (r1 , s1)) (cons-⟨,⟩ (r2 , s2)) 
        with bRa r1 r2 | cSa s1 s2
      prop b c a _ _ (cons-⟨,⟩ (r1 , s1)) (cons-⟨,⟩ (.r1 , .s1))| refl | refl 
        = cong cons-⟨,⟩ refl

  ⟨,⟩-isDec : {A B C : Set}{R : Rel A B}{S : Rel A C}
            → {{ decR : IsDec R }} {{ decS : IsDec S }}
            → IsDec ⟨ R , S ⟩
  ⟨,⟩-isDec ⦃ dec dR ⦄ ⦃ dec dS ⦄ 
    = dec (λ { (b , c) a → decide b c a (dR b a) (dS c a) })
    where
      decide : {A B C : Set}{R : Rel A B}{S : Rel A C}
             → (b : B)(c : C)(a : A) → Dec (R b a) → Dec (S c a)
             → Dec (⟨ R , S ⟩ (b , c) a)
      decide b c a (yes r) (yes s) = yes (cons-⟨,⟩ (r , s))
      decide b c a (no ¬r) _       = no (λ z → ¬r (p1 (⟨_,_⟩.un z)))
      decide b c a _       (no ¬s) = no (λ z → ¬s (p2 (⟨_,_⟩.un z)))

-- Relational product
_*_ : {A B C D : Set} → Rel A B → Rel C D → Rel (A × C) (B × D)
(R * S) = ⟨ R ∙ π₁ , S ∙ π₂ ⟩

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
         let wita , witb  = p1∙ hip -- the pair witnessing the composition. 
             aπ₁ab , abXc = p2∙ hip
             k = pair-lemma-l (p1∙ hip) a (fun.un aπ₁ab)
         in p1 (⟨_,_⟩.un (prf c (a , witb) (subst (λ x → X x c) k abXc)))
  ) where
    pair-lemma-l : {A B : Set} → (h : A × B) → (x : A) → p1 h ≡ x → h ≡ (x , p2 h)
    pair-lemma-l h .(p1 h) refl = refl


prod-uni-r2 : ∀{A B C} → {X : Rel C (A × B)}
            → (R : Rel C A) → (S : Rel C B)
            → X ⊆ ⟨ R , S ⟩
            → π₂ ∙ X ⊆ S
prod-uni-r2 {X = X} r s (⊆in prf)
  = ⊆in (λ c b hip → 
         let wita , witb  = p1∙ hip 
             bπ₂ab , abXc = p2∙ hip
             k = pair-lemma-r (p1∙ hip) b (fun.un bπ₂ab)
         in p2 (⟨_,_⟩.un (prf c (wita , b) (subst (λ x → X x c) k abXc)))
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
         in cons-⟨,⟩ ((⊆out pr) c a (ab , cons-fun refl , hip) , (⊆out ps) c b (ab , cons-fun refl , hip)))

----------------------------
-- * General Properties * --
----------------------------

id*id≡id : {A B : Set} → Id * Id ≡r Id {A × B}
id*id≡id {A} {B} = ⊆in aux1 , ⊆in aux2
  where
    aux1 : (a b : A × B) → (Id * Id) b a → Id b a
    aux1 a b (cons-⟨,⟩ ((w1 , c11 , c12) , (w2 , c21 , c22))) 
      rewrite sym (fun.un c11)
            | sym (fun.un c21)
            | sym (fun.un c12)
            | sym (fun.un c22)
            = cons-fun (cong₂ _,_ (fun.un c11) (fun.un c21))

    aux2 : (a b : A × B) → Id b a → (Id * Id) b a
    aux2 a b (cons-fun a≡b) rewrite a≡b 
      = cons-⟨,⟩ ( (p1 b , cons-fun refl , cons-fun refl) 
                 , p2 b , cons-fun refl , cons-fun refl)
