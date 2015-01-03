\begin{code}
open import Data.Bool using (Bool; true; false)
open import Relation.Binary.PropositionalEquality
open import Data.Product using (_×_; ∃; _,_; Σ) renaming (proj₁ to p1; proj₂ to p2)
open import Data.Sum using (_⊎_; [_,_]) renaming (inj₁ to i1; inj₂ to i2; [_,_]′ to case)
open import Function using (id; _∘_)

open import Data.Unit using (Unit; unit)
open import Data.Empty using (⊥; ⊥-elim)

open import Level using (Level; zero; _⊔_; suc)

open import Relation.Binary.Core hiding (Rel)
open import Relation.Nullary.Core
open import Relation.Nullary.Decidable
\end{code}

%<*homotopy-def>
\begin{code}
_~_ : {A : Set}{B : A → Set}(f g : (x : A) → B x) → Set
f ~ g = ∀ x → f x ≡ g x
\end{code}
%</homotopy-def>

\begin{code}
~-refl : {A : Set}{B : A → Set}{f : (x : A) → B x} → f ~ f
~-refl = λ x → refl

~-sym : {A : Set}{B : A → Set}{f g : (x : A) → B x} → f ~ g → g ~ f
~-sym prf = λ x → sym (prf x)

~-trans : {A : Set}{B : A → Set}{f g h : (x : A) → B x}
        → f ~ g → g ~ h → f ~ h
~-trans fg gh = λ x → trans (fg x) (gh x)
\end{code}

%<*isequiv-def>
\begin{code}
isequiv : {A B : Set}(f : A → B) → Set
isequiv f = ∃ (λ g → ((f ∘ g) ~ id) × ((g ∘ f) ~ id))
\end{code}
%</isequiv-def>

%<*univalence-def>
\begin{code}
_≈_ : (A B : Set) → Set
A ≈ B = ∃ (λ f → isequiv f)
\end{code}
%</univalence-def>

\begin{code}
≈-refl : {A : Set} → A ≈ A
≈-refl = id , id , (λ _ → refl) , (λ _ → refl)

≈-sym : {A B : Set} → A ≈ B → B ≈ A
≈-sym (ab , (ba , isequiv-ab)) 
  = ba , ab , p2 isequiv-ab , p1 isequiv-ab

≈-trans : {A B C : Set} → A ≈ B → B ≈ C → A ≈ C
≈-trans (ab , (ba , isequiv-ab)) (bc , (cb , isequiv-cb))
  = bc ∘ ab , ba ∘ cb 
  , quasi-inv cb bc ba ab (p1 isequiv-cb) (p1 isequiv-ab) 
  , quasi-inv ab ba bc cb (p2 isequiv-ab) (p2 isequiv-cb)
  where
    quasi-inv : {A B C : Set}
                  (f : A → B)(f̅ : B → A)(g : B → C)(g̅ : C → B) 
                → ((f̅ ∘ f) ~ id) → ((g̅ ∘ g) ~ id)
                → (f̅ ∘ g̅ ∘ g ∘ f) ~ id
    quasi-inv f if g ig prff prfg x 
      rewrite prfg (f x) 
            | prff x 
            = refl
\end{code}

%<*isprop-def>
\begin{code}
isProp : ∀{a} → Set a → Set a
isProp P = (p₁ p₂ : P) → p₁ ≡ p₂ 
\end{code}
%</isprop-def>

%<*lemma-332>
\begin{code}
lemma-332 : {P : Set} → isProp P → (p₀ : P) → P ≈ Unit
\end{code}
%</lemma-332>

\begin{code}
lemma-332 {P = P} prop prf = isequiv-p→1 prop prf
  where
    quasi-inv-1 : {P : Set}(f : P → Unit) → (g : Unit → P) → (f ∘ g) ~ id
    quasi-inv-1 f g unit with g unit | f (g unit)
    ...| gu | unit = refl

    quasi-inv-2 : {P : Set} → isProp P → (f : Unit → P) → (g : P → Unit) → (f ∘ g) ~ id
    quasi-inv-2 prf f g x with g x
    ...| gx with f gx
    ...| fgx = prf fgx x

    isequiv-p→1 : {P : Set} → isProp P → P → Σ (P → Unit) (λ f → isequiv f)
    isequiv-p→1 prf p₀ 
      = let
        p1 = λ _ → unit
        1p = λ _ → p₀
      in p1 , 1p , quasi-inv-1 p1 1p , quasi-inv-2 prf 1p p1
\end{code}

%<*not-lemma-332>
\begin{code}
¬lemma-332 : {P : Set} → isProp P → (P → ⊥) → P ≈ ⊥
\end{code}
%</not-lemma-332>

\begin{code}
¬lemma-332 {P} prp f = f , (λ ()) , (λ ()) , (⊥-elim ∘ f) 
\end{code}

%<*univalence-axiom>
\begin{code}
postulate
  ≈-to-≡ : {A B : Set} → (A ≈ B) → A ≡ B
\end{code}
%</univalence-axiom>

\begin{code}
Rel : Set → Set → Set1
Rel A B = REL B A zero

infix 6 _⊆_
\end{code}

%<*instances>
\begin{code}
record IsProp {A B : Set}(R : Rel A B) : Set where
  constructor mp
  field isprop : ∀ b a → isProp (R b a) 

record IsDec {A B : Set}(R : Rel A B) : Set where
  constructor dec
  field undec : Decidable R
    
open IsDec {{...}}
open IsProp {{...}}
\end{code}
%</instances>

%<*subrel-def>
\begin{code}
data _⊆_ {A B : Set}(R S : Rel A B) : Set where
  ⊆in : (∀ a b → R b a → S b a) → R ⊆ S
\end{code}
%</subrel-def>

%<*subrel-antisym>
\begin{code}
⊆-antisym : {A B : Set}{R S : Rel A B} 
            {{ decr : IsDec R }} {{ decs : IsDec S }}
            {{ pir : IsProp R }} {{ pis : IsProp S }}
          → R ⊆ S → S ⊆ R → R ≡ S
\end{code}
%</subrel-antisym>
\begin{code}
⊆-antisym {R = R} {S = S} {{ dec dr }} {{ dec ds }} {{ mp pir }} {{ mp pis }} (⊆in rs) (⊆in sr)
  = rel-extensionality (λ b a 
  → let
      propS = pis b a
      propR = pir b a
    in case-analisys {R = R} {S = S} b a (rs a b) (sr a b) propR propS (dr b a) (ds b a))
  where
    postulate
      rel-extensionality : {A B : Set}{R S : Rel A B}
                         → (∀ b a → R b a ≡ S b a)
                         → R ≡ S
                         
    case-analisys : {A B : Set}{R S : Rel A B}
                  → (b : B)(a : A)
                  → (R b a → S b a)
                  → (S b a → R b a)
                  → isProp (R b a)
                  → isProp (S b a)
                  → Dec (R b a) → Dec (S b a)
                  → R b a ≡ S b a
    case-analisys b a rs sr pr ps (yes bRa)  (yes bSa)  
      with ≈-to-≡ (lemma-332 pr bRa) | ≈-to-≡ (lemma-332 ps bSa)
    ...| ur | us = trans ur (sym us)
    case-analisys b a rs sr pr ps (yes bRa) (no ¬bSa) = ⊥-elim (¬bSa (rs bRa))
    case-analisys b a rs sr pr ps (no ¬bRa) (yes bSa) = ⊥-elim (¬bRa (sr bSa))
    case-analisys b a rs sr pr ps (no ¬bRa) (no ¬bSa) 
      with ≈-to-≡ (¬lemma-332 pr ¬bRa) | ≈-to-≡ (¬lemma-332 ps ¬bSa)
    ...| ur | us = trans ur (sym us)
\end{code}


