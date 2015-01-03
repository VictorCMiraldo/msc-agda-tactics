\begin{code}
open import Data.Bool using (Bool; true; false; T; not) renaming (_∨_ to or; _∧_ to and)
open import Relation.Binary.PropositionalEquality
open import Data.Product using (Σ; _×_; _,_; ∃; proj₁; proj₂)
open import Data.Sum using (_⊎_; [_,_]) renaming (inj₁ to i1; inj₂ to i2; [_,_]′ to case)
open import Function using (id; _∘_)

open import Data.Unit using (Unit; unit)
open import Data.Empty using (⊥)
\end{code}


%<*data-truncation>
\begin{code}
data ||_|| (A : Set) : Set where
  one : A → || A ||

postulate
  truncation-post : {A : Set}(x y : || A ||) → x ≡ y
\end{code}
%</data-truncation>

%<*data-U>
\begin{code}
mutual
  data U : Set where
    TT  : U
    FF  : U
    _∧_ : U → U → U
    ¬_  : U → U
    _⇒_ : U → U → U
    _∨_ : U → U → U
    all : {A : U} → (♯ A → U) → U
    exs : {A : U} → (♯ A → U) → U
    _==_  : {A : U}(x y : ♯ A) → U

  {-# TERMINATING #-}
  ♯_ : U → Set
  ♯ TT = Unit
  ♯ FF = ⊥
  ♯ (p ∧ q) = ♯ p × ♯ q
  ♯ (¬ p) = ♯ p → ⊥
  ♯ (p ⇒ q) = ♯ p → ♯ q
  ♯ (p ∨ q) = || ♯ p ⊎ ♯ q ||
  ♯ all p = ∀ a → ♯ p a
  ♯ exs {A} p = || ∃ (♯_ ∘ p) || 
  ♯ (x == y) = x ≡ y
\end{code}
%</data-U>


%<*isProp-def>
\begin{code}
isProp : (P : Set) → Set
isProp P = (x y : P) → x ≡ y
\end{code}
%</isProp-def>

%<*homotopy-def>
\begin{code}
_~_ : {A : Set}{B : A → Set}(f g : (x : A) → B x) → Set
f ~ g = ∀ x → f x ≡ g x
\end{code}
%</homotopy-def>

%<*isequiv-def>
\begin{code}
isequiv : {A B : Set}(f : A → B) → Set
isequiv f = ∃ (λ g → ((f ∘ g) ~ id) × ((g ∘ f) ~ id))
\end{code}
%</isequiv-def>

%<*uprop-decl>
\begin{code}
uProp : (P : U) → isProp (♯ P)
\end{code}
%</uprop-decl>
\begin{code}
uProp = ?
\end{code}

