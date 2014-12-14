module Rel.Properties where

open import Data.Bool using (Bool; true; false)
open import Relation.Binary.PropositionalEquality
open import Data.Product using (_×_; ∃; _,_) renaming (proj₁ to p1; proj₂ to p2; map to _><_)
open import Data.Sum using (_⊎_; [_,_]) renaming (inj₁ to i1; inj₂ to i2; [_,_]′ to case)
open import Function using (id; _∘_; _$_)

open import Data.Unit using (Unit; unit)
open import Data.Empty using (⊥; ⊥-elim)

open import Rel.Core.Core
open import Rel.Core.Correflexive
open import Rel.Core.Equality

----------------------------
-- * Trivial Properties * --
----------------------------

R⊆Top : ∀{A B : Set}{R : Rel A B}
      → R ⊆ Top
R⊆Top = ⊆in (λ _ _ _ → unit) 

Bot⊆R : ∀{A B : Set}{R : Rel A B}
      → Bot ⊆ R
Bot⊆R = ⊆in (λ _ _ → λ ())

⊆-upper-bound : {A B : Set}{R S S' : Rel A B}
              → S ⊆ S' → R ⊆ S → R ⊆ S'
⊆-upper-bound ss' rs = ⊆-trans rs ss'

---------------------------------
-- * Correflexive Properties * --
---------------------------------

{-
φ-intro-r : ∀{A B}(P : A → Set)(a : A)(b : B)
          → ((φ P) ∙ Top) a b ≡ P a
φ-intro-r p a b with φ p 
...| q = {!!}
-}


φ⊆Id : ∀{A : Set}{P : A → Set}
     → φ P ⊆ Id
φ⊆Id = ⊆in (λ b b′ bφb → cons-fun $ sym (p1 (φ.un bφb)))

ρ-intro : ∀{A B : Set}(R : Rel A B)
        → R ≡r ρ R ∙ R
ρ-intro r 
        = ⊆in (λ a b bRa → b , cons-∩ ((a , bRa , bRa) , cons-fun refl) , bRa)
        , ⊆in (λ a b bρRRa → subst (λ x → r x a) (fun.un $ p2∩ (p1 (p2∙ bρRRa))) (p2 (p2∙ bρRRa)))

----------------------
-- * Composition  * --
----------------------

-- Relational composition is left associative
∙-assocl : ∀{A B C D}{R : Rel A B}{S : Rel B C}{T : Rel C D}
         → T ∙ (S ∙ R) ⊆ (T ∙ S) ∙ R
∙-assocl = ⊆in (λ a d hip 
  → let (c , dTc , b , cSb , bRa) = hip
    in b , (c , dTc , cSb) , bRa)

-- And right associative
∙-assocr : ∀{A B C D}{R : Rel A B}{S : Rel B C}{T : Rel C D}
         → (T ∙ S) ∙ R ⊆ T ∙ (S ∙ R)
∙-assocr = ⊆in (λ a d hip
  → let (b , (c , dTc , cSb) , bRa) = hip
    in c , dTc , b , cSb , bRa)

-- Wrapper for associativity
∙-assoc : ∀{A B C D}{R : Rel A B}{S : Rel B C}{T : Rel C D}
        → (T ∙ S) ∙ R ≡r T ∙ (S ∙ R)
∙-assoc = ≡r-intro ∙-assocr ∙-assocl

-- Id is left neutral
∙-id-l : ∀{A B}{R : Rel A B}
       → R ≡r Id ∙ R
∙-id-l {R = R}
       = ⊆in (λ a b bRa → b , cons-fun refl , bRa) 
       , ⊆in (λ a b bIdRa → subst (λ x → R x a) (fun.un $ p1 (p2∙ bIdRa)) (p2 (p2∙ bIdRa)) )

-- Id is right neutral
∙-id-r : ∀{A B}(R : Rel A B)
       → R ≡r R ∙ Id
∙-id-r R = ⊆in (λ a b bRa → a , bRa , cons-fun refl)
         , ⊆in (λ a b bRIda → subst (R b) (sym (fun.un $ p2 (p2∙ bRIda))) (p1 (p2∙ bRIda)) )

∙-monotony : ∀{A B C}{S T : Rel B C}{Q R : Rel A B}
           → (S ⊆ T) × (Q ⊆ R) → S ∙ Q ⊆ T ∙ R
∙-monotony (⊆in s⊆t , ⊆in q⊆r) = ⊆in (λ a c bSQa
  → let b   = p1∙ bSQa
        cSb = p1 (p2∙ bSQa)
        bQa = p2 (p2∙ bSQa)
    in b , s⊆t b c cSb , q⊆r a b bQa)


-------------------------------
-- * Knapking and Shunting * --
-------------------------------


shunting-l-1 : ∀{A B C}{R : Rel A B}{f : B → C}{S : Rel A C}
             → (fun f) ∙ R ⊆ S
             → R ⊆ (fun f)ᵒ ∙ S
shunting-l-1 {f = f} (⊆in hip)
  = ⊆in (λ a b bRa → f b , cons-fun refl , hip a (f b) (b , cons-fun refl , bRa)) 

shunting-l-2 : ∀{A B C}{R : Rel A B}{f : B → C}{S : Rel A C}
             → R ⊆ (fun f)ᵒ ∙ S
             → (fun f) ∙ R ⊆ S
shunting-l-2 {f = f}{S = S} (⊆in hip)
  = ⊆in (λ a c bfRa →
         let aux = hip a (p1∙ bfRa) (p2 (p2∙ bfRa))
             r   = p2 (p2∙ aux)
         in subst (λ k → S k a) (
             subst (λ x → x ≡ c) (fun.un (p1 (p2∙ aux))) (fun.un (p1 (p2∙ bfRa)))
            ) r
         )

shunting-r-1 : ∀{A B C}{R : Rel A B}{f : A → C}{S : Rel C B}
             → R ∙ (fun f)ᵒ ⊆ S
             → R ⊆ S ∙ (fun f) 
shunting-r-1 {f = f} (⊆in hip)
  = ⊆in (λ a b bRa → f a , hip (f a) b (a , bRa , cons-fun refl) , cons-fun refl)

shunting-r-2 : ∀{A B C}{R : Rel A B}{f : A → C}{S : Rel C B}
             → R ⊆ S ∙ (fun f) 
             → R ∙ (fun f)ᵒ ⊆ S
shunting-r-2 {f = f}{S = S} (⊆in hip) 
  = ⊆in (λ c b bRfa →
         let aux = hip (p1∙ bRfa) b (p1 (p2∙ bRfa))
             r   = p1 (p2∙ aux)
         in subst (S b) (
                  subst (λ x → x ≡ c) (fun.un (p2 (p2∙ aux))) (fun.un (p2 (p2∙ bRfa)))
            ) r
         )

-------------------
-- * Converses * --
-------------------

ᵒ-distr : ∀{A B C}{R : Rel A B}{S : Rel B C}
          → (S ∙ R) ᵒ ≡r R ᵒ ∙ S ᵒ
ᵒ-distr 
  = ⊆in (λ c a bSRoa → p1∙ bSRoa , p2 (p2∙ bSRoa) , p1 (p2∙ bSRoa))
  , ⊆in (λ c a bSoRoa → p1∙ bSoRoa , p2 (p2∙ bSoRoa) , p1 (p2∙ bSoRoa))


ᵒ-fun-identity-r : {A B : Set}{f : A → B}
                 → (fun f) ∙ (fun f)ᵒ ⊆ Id
ᵒ-fun-identity-r {f = f}
                 = ⊆in (λ b' b hip → cons-fun $ fun-is-simple {f = f} (p1∙ hip) b b' (p1 (p2∙ hip)) (p2 (p2∙ hip)))
  where
    fun-is-simple : {A B : Set}{f : A → B}(a : A)(b b' : B)
                  → (fun f) b a → (fun f) b' a → id b' ≡ b
    fun-is-simple _ _ _ bfa b'fa = trans (sym (fun.un b'fa)) (fun.un bfa)

-- Indirect equality testing

open import Rel.Reasoning.SubsetJudgement

∩-assoc : {A B : Set}{R S T : Rel A B}
        → (R ∩ S) ∩ T ≡i R ∩ (S ∩ T)
∩-assoc {R = r} {S = s} {T = t} x 
  = (begin 
      x ⊆ (r ∩ s) ∩ t 

    ⇐⟨ ∩-uni-r x (r ∩ s) t ⟩ 

      (x ⊆ r ∩ s × x ⊆ t)

    ⇐⟨ ∩-uni-r x r s >< id ⟩

      ((x ⊆ r × x ⊆ s) × x ⊆ t)

    ⇐⟨ ×-assoc-l ⟩

      (x ⊆ r × x ⊆ s × x ⊆ t) 

    ⇐⟨ id >< ∩-uni-l x s t ⟩

      (x ⊆ r × x ⊆ s ∩ t)

    ⇐⟨ ∩-uni-l x r (s ∩ t) ⟩

      x ⊆ r ∩ (s ∩ t)

    ∎)
  , (begin 

      x ⊆ r ∩ (s ∩ t)

    ⇐⟨ ∩-uni-r x r (s ∩ t) ⟩ 

      (x ⊆ r × x ⊆ s ∩ t)

    ⇐⟨ id >< ∩-uni-r x s t ⟩

      (x ⊆ r × x ⊆ s × x ⊆ t)

    ⇐⟨ ×-assoc-r ⟩ 

      ((x ⊆ r × x ⊆ s) × x ⊆ t) 

    ⇐⟨ ∩-uni-l x r s >< id ⟩

      (x ⊆ r ∩ s × x ⊆ t)

    ⇐⟨ ∩-uni-l x (r ∩ s) t ⟩

      x ⊆ (r ∩ s) ∩ t
    ∎)
  where
    ×-assoc-l : {A B C : Set} → (A × B × C) → (A × B) × C
    ×-assoc-l (a , b , c) = ((a , b) , c) 

    ×-assoc-r : {A B C : Set} → (A × B) × C → A × B × C
    ×-assoc-r ((a , b) , c) = (a , b , c)
