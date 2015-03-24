
\begin{code}
open import Prelude
open import RW.Language.RTerm
open import RW.Language.FinTerm
open import RW.Language.RTermUtils
open import RW.Utils.Monads
open import Data.Nat as Nat using (ℕ; suc; zero; _+_; _⊔_; decTotalOrder; _<_; _≤_; s≤s; z≤n) renaming (_≟_ to _≟-ℕ_)
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_; refl; cong; sym; trans; subst)
open PropEq.≡-Reasoning
open import Function using (_∘_; id; flip; _$_)

open Monad {{...}}

+-suc : ∀ m n → m + suc n ≡ suc (m + n)
+-suc zero    n = refl
+-suc (suc m) n = cong suc (+-suc m n)
\end{code}

%<*id-def>
\begin{code}
+-id : ∀ n → n + 0 ≡ n
\end{code}
%</id-def>
\begin{code}
+-id zero = refl
+-id (suc n) = cong suc $ +-id n
\end{code}

%<*assoc-def>
\begin{code}
+-assoc : ∀ m n o → (m + n) + o ≡ m + (n + o)
\end{code}
%</assoc-def>
\begin{code}
+-assoc zero    _ _ = refl
+-assoc (suc m) n o = cong suc $ +-assoc m n o
\end{code}

%<*comm-def>
\begin{code}
+-comm : ∀ m n → m + n ≡ n + m
\end{code}
%</comm-def>
\begin{code}
+-comm zero    n = sym $ +-id n
+-comm (suc m) n =
  begin
    suc m + n
  ≡⟨ refl ⟩
    suc (m + n)
  ≡⟨ cong suc (+-comm m n) ⟩
    suc (n + m)
  ≡⟨ sym (+-suc n m) ⟩
    n + suc m
  ∎
\end{code}

%<*exch-law-type>
\begin{code}
exch : (x y : ℕ) → x + y ≡ y + (x + 0)
\end{code}
%</exch-law-type>

%<*exch-law-impl-1>
\begin{code}
exch x y = trans (+-comm x y) (cong (λ w → y + w) (sym (+-id x)))
\end{code}
%</exch-law-impl-1>

%<*subst-def>
\begin{code}
_[_] : {A : Set}{{eqA : Eq A}} → RTerm A → RTerm A × RTerm A → NonDet (RTerm A)
\end{code}
%</subst-def>
\begin{code}
_[_] = ?
\end{code}

%<*apply-def>
\begin{code}
{-# TERMINATING #-}
apply : {n : ℕ} → RTerm ⊥ → RBinApp (Fin n) → NonDet (RTerm ⊥)
\end{code}
%</apply-def>
\begin{code}
apply = ?
\end{code}

%<*divideGoal-def>
\begin{code}
divideGoal : RBinApp ⊥ → List (Σ ℕ (RBinApp ∘ Fin)) → Maybe (List (RTerm ⊥))
\end{code}
%</divideGoal-def>
\begin{code}
divideGoal = ?
\end{code}


