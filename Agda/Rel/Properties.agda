module Rel.Properties where

open import Data.Bool using (Bool; true; false)
open import Relation.Binary.PropositionalEquality
open import Data.Product using (_×_; ∃; _,_) renaming (proj₁ to p1; proj₂ to p2)
open import Data.Sum using (_⊎_; [_,_]) renaming (inj₁ to i1; inj₂ to i2; [_,_]′ to case)
open import Function using (id; _∘_)

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
φ⊆Id = ⊆in (λ b b′ bφb → sym (p1 bφb))

ρ-intro : ∀{A B : Set}(R : Rel A B)
        → R ≡r ρ R ∙ R
ρ-intro r 
        = ⊆in (λ a b bRa → b , ((a , bRa , bRa) , refl) , bRa)
        , ⊆in (λ a b bρRRa → subst (λ x → r x a) (p2 (p1 (p2 bρRRa))) (p2 (p2 bρRRa)))
  
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

{-
-- Id is left neutral
∙-id-l : ∀{A B}{R : Rel A B}
       → R ≡r Id ∙ R
∙-id-l {R = R}
       = (λ b a bRa → b , refl , bRa) 
       , (λ b a bIdRa → subst (λ x → R x a) (p1 (p2 bIdRa)) (p2 (p2 bIdRa)))
-}

-- Id is right neutral
∙-id-r : ∀{A B}(R : Rel A B)
       → R ≡r R ∙ Id
∙-id-r R = ⊆in (λ a b bRa → a , bRa , refl)
         , ⊆in (λ a b bRIda → subst (R b) (sym (p2 (p2 bRIda))) (p1 (p2 bRIda)))

∙-monotony : ∀{A B C}{S T : Rel B C}{Q R : Rel A B}
           → (S ⊆ T) × (Q ⊆ R) → S ∙ Q ⊆ T ∙ R
∙-monotony (⊆in s⊆t , ⊆in q⊆r) = ⊆in (λ a c bSQa
  → let b   = p1 bSQa
        cSb = p1 (p2 bSQa)
        bQa = p2 (p2 bSQa)
    in b , s⊆t b c cSb , q⊆r a b bQa)

{-
∙-subst-r : ∀{A B C}{R : Rel B C}{T U : Rel A B}
          → T ≡r U → R ∙ T ⊆ R ∙ U
∙-subst-r (t⊆u , u⊆t) 
  = λ c a bRTa →
    let b   = p1 bRTa 
        cRb = p1 (p2 bRTa)
    in b , cRb , t⊆u b a (p2 (p2 bRTa))

∙-subst-l : ∀{A B C}{T U : Rel B C}{R : Rel A B}
          → T ≡r U → T ∙ R ⊆ U ∙ R
∙-subst-l (t⊆u , u⊆t)
  = λ c a bTRa → 
    let b   = p1 bTRa
        cTb = p1 (p2 bTRa)
    in b , t⊆u c b cTb , p2 (p2 bTRa)

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

-------------------
-- * Converses * --
-------------------

ᵒ-distr : ∀{A B C}{R : Rel A B}{S : Rel B C}
          → (S ∙ R) ᵒ ≡r R ᵒ ∙ S ᵒ
ᵒ-distr 
  = (λ a c bSRoa → p1 bSRoa , p2 (p2 bSRoa) , p1 (p2 bSRoa))
  , (λ a c bSoRoa → p1 bSoRoa , p2 (p2 bSoRoa) , p1 (p2 bSoRoa))

ᵒ-fun-identity-r : {A B : Set}{f : A → B}
                 → (fun f) ∙ (fun f)ᵒ ⊆ Id
ᵒ-fun-identity-r {f = f}
  = λ b b' hip → fun-is-simple {f = f} (p1 hip) b b' (p1 (p2 hip)) (p2 (p2 hip))
  where
    fun-is-simple : {A B : Set}{f : A → B}(a : A)(b b' : B)
                  → (fun f) b a → (fun f) b' a → id b' ≡ b
    fun-is-simple _ _ _ bfa b'fa = trans (sym b'fa) bfa

-}
