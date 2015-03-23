\begin{code}
open import Prelude renaming (_++_ to _++-List_)
open import Data.Maybe using (Maybe; just; nothing; maybe; From-just)
open import Data.Fin using (Fin; toℕ) renaming (inject+ to finject; raise to fraise; zero to fzero; suc to fsuc)
open import Data.List.All as A
open import Data.Vec using (Vec; _∷_; [])

open import Data.Nat renaming (decTotalOrder to decTotalOrder-ℕ)
open import Relation.Binary using (module DecTotalOrder)


open import RW.Language.RTerm
-- open import RW.Language.FinTerm

--------------------------------------------------
-- Monadic Boilerplate

open import RW.Utils.Monads
open Monad {{...}}

_<$>_ : ∀{a b}{A : Set a}{B : Set b} 
      → (A → B) → Maybe A → Maybe B
_ <$> nothing  = nothing
f <$> (just x) = just (f x)

_<*>_ : ∀{a b}{A : Set a}{B : Set b}
      → Maybe (A → B) → Maybe A → Maybe B
just f <*> just x = just (f x)
_      <*> _      = nothing

mapM : {A B : Set} → (A → Maybe B) → List A → Maybe (List B)
mapM f = Prelude.foldr 
         (λ a → maybe (λ x → flip _∷_ x <$> f a) nothing) 
         (just [])
\end{code}

%<*finterm-def>
\begin{code}
FinTerm : ℕ → Set
FinTerm = RTerm ∘ Fin
\end{code}
%</finterm-def>

%<*X-def>
\begin{code}
X : ℕ → Set
X = Vec (Maybe (RTerm ⊥))
\end{code}
%</X-def>

%<*empty-X-def>
\begin{code}
empty-X : {n : ℕ} → X n
empty-X {zero}  = []
empty-X {suc n} = nothing ∷ empty-X
\end{code}
%</empty-X-def>

%<*lookup-X-def>
\begin{code}
lookup-X : {n : ℕ} → Fin n → X n → Maybe (RTerm ⊥)
lookup-X fz     (x ∷ _) = x
lookup-X (fs i) (_ ∷ s) = lookup-X i s
\end{code}
%</lookup-X-def>

%<*apply-X-def>
\begin{code}
{-# TERMINATING #-}
apply-X : {n : ℕ} → X n → FinTerm n → Maybe (RTerm ⊥)
apply-X s (ovar x) = lookup-X x s
apply-X s (ivar n) = just (ivar n)
apply-X s (rlit l) = just (rlit l)
apply-X s (rlam t) = rlam <$> apply-X s t
apply-X s (rapp n ts) = rapp n <$> mapM (apply-X s) ts
\end{code}
%</apply-X-def>


%<*extend-X-def>
\begin{code}
extend-X : {n : ℕ} → Fin n → RTerm ⊥ → X n → Maybe (X n)
extend-X fz t (nothing ∷ s) = just (just t ∷ s)
extend-X fz t (just t′ ∷ s) with t ≟-RTerm t′
...| yes _ = just (just t ∷ s)
...| no  _ = nothing
extend-X (fs i) t (mt ∷ s) = _∷_ mt <$> extend-X i t s
\end{code}
%</extend-X-def>


%<*instantiation>
\begin{code}
mutual
  instAcc : {n : ℕ} → FinTerm n → RTerm ⊥ → X n → Maybe (X n)
  instAcc (ovar x) t s = extend-X x t s
  instAcc (ivar _) _ s = just s
  instAcc (rlit l) (rlit k) s with l ≟-Lit k 
  ...| yes _ = just s
  ...| no  _ = nothing
  instAcc (rlam t) (rlam u) s = instAcc t u s
  instAcc (rapp n ts) (rapp m us) s with n ≟-RTermName m
  ...| no  _ = nothing
  ...| yes _ = instAcc* ts us s
  instAcc _ _ _ = nothing

  instAcc* : {n : ℕ} → List (FinTerm n) → List (RTerm ⊥) → X n → Maybe (X n)
  instAcc* [] [] s = just s
  instAcc* [] (_ ∷ _) _ = nothing
  instAcc* (_ ∷ _) [] _ = nothing
  instAcc* (x ∷ xs) (y ∷ ys) s = instAcc x y s >>= instAcc* xs ys

inst : {n : ℕ} → FinTerm n → RTerm ⊥ → Maybe (X n)
inst t u = instAcc t u empty-X
\end{code}
%</instantiation>

%<*rsubst-def>
\begin{code}
RSubst : Set
RSubst = List (ℕ × RTerm ⊥)
\end{code}
%</rsubst-def>

%<*rsubst-concat>
\begin{code}
_++ₓ_ : {n : ℕ} → X n → X n → Maybe (X n)
[]       ++ₓ []       = just []
(x ∷ xs) ++ₓ (y ∷ ys) with x | y
...| nothing | just y' = _∷_ y <$> (xs ++ₓ ys)
...| just x' | nothing = _∷_ x <$> (xs ++ₓ ys)
...| nothing | nothing = nothing
...| just x' | just y' with x' ≟-RTerm y'
...| no _  = nothing
...| yes _ = _∷_ x <$> (xs ++ₓ ys)
\end{code}
%</rsubst-concat>

