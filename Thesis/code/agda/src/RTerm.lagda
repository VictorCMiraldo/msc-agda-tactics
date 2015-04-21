\begin{code}
open import Prelude
open import Level using (Level) renaming (zero to lz; suc to ls)
open import Data.List.Properties as ListProps renaming (∷-injective to ∷-inj)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.String
open import Data.Nat as Nat using (decTotalOrder; _≤_; s≤s; z≤n; _≤?_)
open import Relation.Binary using (module DecTotalOrder)
open import Reflection renaming (Term to AgTerm; Type to AgType)

open Eq {{...}}
\end{code}

%<*rtermname-data>
\begin{code}
data RTermName : Set where
    rcon : Name → RTermName
    rdef : Name → RTermName
    impl : RTermName
\end{code}
%</rtermname-data>

%<*rterm-data>
\begin{code}
data RTerm {a}(A : Set a) : Set a where
    ovar : (x : A) → RTerm A
    ivar : (n : ℕ) → RTerm A
    rlit : (l : Literal) → RTerm A
    rlam : RTerm A → RTerm A
    rapp : (n : RTermName)(ts : List (RTerm A)) → RTerm A
\end{code}
%</rterm-data>

\begin{code}
isHole : ∀{a}{A : Set a} → RTerm (Maybe A) → Bool
isHole (ovar nothing) = true
isHole _              = false
\end{code}

\begin{code}
{-# TERMINATING #-}
\end{code}
%<*rterm-replace>
\begin{code}
replace : ∀{a b}{A : Set a}{B : Set b}
        → (ovar-f : A → RTerm B)
        → (ivar-f : ℕ → RTerm B)
        → RTerm A → RTerm B
replace f g (ovar x) = f x
replace f g (ivar n) = g n
replace _ _ (rlit l) = rlit l
replace f g (rlam x) = rlam (replace f g x)
replace f g (rapp n ts) = rapp n (map (replace f g) ts)  
\end{code}
%</rterm-replace>

%<*rterm-fmap>
\begin{code}
replace-A : ∀{a b}{A : Set a}{B : Set b} 
          → (A → RTerm B) → RTerm A → RTerm B
replace-A f = replace f ivar

_◇-A_ : ∀{a b c}{A : Set a}{B : Set b}{C : Set c}
      → (B → RTerm C) → (A → RTerm B)
      → A → RTerm C
f ◇-A g = replace-A f ∘ g
\end{code}
%</rterm-fmap>

%<*rterm-intersect-type>
\begin{code}
_∩_ : ∀{A} ⦃ eqA : Eq A ⦄ 
    → RTerm A → RTerm A → RTerm (Maybe A)
\end{code}
%</rterm-intersect-type>
\begin{code}
_∩_ = ?
\end{code}

%<*rterm-difference-type>
\begin{code}
_-_ : ∀{A} ⦃ eqA : Eq A ⦄ 
    → RTerm (Maybe A) → RTerm A → Maybe (List (RTerm A))
\end{code}
%</rterm-difference-type>
\begin{code}
_-_ = ?
\end{code}

\begin{code}
{-# TERMINATING #-}
\end{code}
%<*lift-ivar-def>
\begin{code}
lift-ivar : RTerm ⊥ → RTerm ℕ
lift-ivar = lift-ivar' 0
  where
    lift-ivar' : ℕ → RTerm ⊥ → RTerm ℕ
    lift-ivar' _ (ovar ())
    lift-ivar' d (ivar n) with d ≤? n
    ...| yes _ = ovar n
    ...| no  _ = ivar n
    lift-ivar' _ (rlit l) = rlit l
    lift-ivar' d (rlam t) = rlam (lift-ivar' (suc d) t)
    lift-ivar' d (rapp n ts) = rapp n (map (lift-ivar' d) ts)
\end{code}
%</lift-ivar-def>


