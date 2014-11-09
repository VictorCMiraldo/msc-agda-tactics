module Rel.Properties where

open import Data.Bool using (Bool; true; false)
open import Relation.Binary.PropositionalEquality
open import Data.Product using (_×_; ∃; _,_) renaming (proj₁ to p1; proj₂ to p2)
open import Data.Sum using (_⊎_; [_,_]) renaming (inj₁ to i1; inj₂ to i2; [_,_]′ to case)
open import Function using (id; _∘_)

open import Data.Unit using (Unit; unit)
open import Data.Empty using (⊥; ⊥-elim)


open import Rel.Core

----------------------------
-- * Trivial Properties * --
----------------------------

R⊆Top : ∀{A B : Set}{R : Rel A B}
      → R ⊆ Top
R⊆Top _ _ _ = unit 

Bot⊆R : ∀{A B : Set}{R : Rel A B}
      → Bot ⊆ R
Bot⊆R _ _ ()

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
φ⊆Id b b′ bφb = sym (p1 bφb)

ρ-intro : ∀{A B : Set}(R : Rel A B)
        → R ≡r ρ R ∙ R
ρ-intro r 
        = (λ b a bRa → b , ((a , bRa , bRa) , refl) , bRa)
        , (λ b a bρRRa → subst (λ x → r x a) (p2 (p1 (p2 bρRRa))) (p2 (p2 bρRRa)))
  

----------------------
-- * Composition  * --
----------------------

-- Relational composition is left associative
∙-assocl : ∀{A B C D}{R : Rel A B}{S : Rel B C}{T : Rel C D}
         → T ∙ (S ∙ R) ⊆ (T ∙ S) ∙ R
∙-assocl d a (c , dTc , b , cSb , bRa) = b , (c , dTc , cSb) , bRa

-- And right associative
∙-assocr : ∀{A B C D}{R : Rel A B}{S : Rel B C}{T : Rel C D}
         → (T ∙ S) ∙ R ⊆ T ∙ (S ∙ R)
∙-assocr d a (b , (c , dTc , cSb) , bRa) = c , dTc , b , cSb , bRa

-- Wrapper for associativity
∙-assoc : ∀{A B C D}{R : Rel A B}{S : Rel B C}{T : Rel C D}
        → (T ∙ S) ∙ R ≡r T ∙ (S ∙ R)
∙-assoc = ≡r-intro ∙-assocr ∙-assocl

-- Id is left neutral
∙-id-l : ∀{A B}{R : Rel A B}
       → R ≡r Id ∙ R
∙-id-l {R = R}
       = (λ b a bRa → b , refl , bRa) 
       , (λ b a bIdRa → subst (λ x → R x a) (p1 (p2 bIdRa)) (p2 (p2 bIdRa)))

-- Id is right neutral
∙-id-r : ∀{A B}{R : Rel A B}
       → R ≡r R ∙ Id
∙-id-r {R = R}
       = (λ b a bRa → a , bRa , refl)
       , (λ b a bRIda → subst (R b) (sym (p2 (p2 bRIda))) (p1 (p2 bRIda)))

∙-monotony : ∀{A B C}{S T : Rel B C}(R : Rel A B)
           → S ⊆ T → S ∙ R ⊆ T ∙ R
∙-monotony _ hip c a bSRa
  = let b = p1 bSRa
        cSb = p1 (p2 bSRa)
        bRa = p2 (p2 bSRa)
    in b , hip c b cSb , bRa

-------------------------------
-- * Knapking and Shunting * --
-------------------------------

shunting-l-1 : ∀{A B C}{R : Rel A B}{f : B → C}{S : Rel A C}
             → (fun f) ∙ R ⊆ S
             → R ⊆ (fun f)ᵒ ∙ S
shunting-l-1 {f = f} hip b a bRa = f b , refl , hip (f b) a (b , refl , bRa) 



shunting-l-2 : ∀{A B C}{R : Rel A B}{f : B → C}{S : Rel A C}
             → R ⊆ (fun f)ᵒ ∙ S
             → (fun f) ∙ R ⊆ S
shunting-l-2 {f = f}{S = S} hip c a bfRa 
  = let aux = hip (p1 bfRa) a (p2 (p2 bfRa))
        r   = p2 (p2 aux)
    in subst (λ k → S k a) (
             subst (λ x → x ≡ c) (p1 (p2 aux)) (p1 (p2 bfRa))
       ) r


shunting-r-1 : ∀{A B C}{R : Rel A B}{f : A → C}{S : Rel C B}
             → R ∙ (fun f)ᵒ ⊆ S
             → R ⊆ S ∙ (fun f) 
shunting-r-1 {f = f} hip b a bRa = f a , hip b (f a) (a , bRa , refl) , refl


shunting-r-2 : ∀{A B C}{R : Rel A B}{f : A → C}{S : Rel C B}
             → R ⊆ S ∙ (fun f) 
             → R ∙ (fun f)ᵒ ⊆ S
shunting-r-2 {f = f}{S = S} hip b c bRfa
  = let aux = hip b (p1 bRfa) (p1 (p2 bRfa))
        r   = p1 (p2 aux)
    in subst (S b) (
             subst (λ x → x ≡ c) (p2 (p2 aux)) (p2 (p2 bRfa))
       ) r

{-
-- TODO: figure how to prove this guys!
knapking-l :  ∀{B C D}{g : D → C}(R : Rel B C)(b : B)(d : D)
           → R (g d) b ≡ ((fun g)ᵒ ∙ R) d b
knapking-l {g = g} r b d with (fun g)ᵒ
...| p = {!!}

knapking : ∀{A B C D}{f : A → B}{g : D → C}(R : Rel B C)(a : A)(d : D)
         → R (g d) (f a) ≡ ((fun g)ᵒ ∙ R ∙ (fun f)) d a
knapking {f = f}{g = g} r a d with ((fun g)ᵒ ∙ r ∙ fun f)
...| p = {!!}
-}
