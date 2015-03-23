
\begin{code}
open import Data.Nat as Nat using (ℕ; suc; zero; _+_; _⊔_; decTotalOrder; _<_; _≤_; s≤s; z≤n) renaming (_≟_ to _≟-ℕ_)
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_; refl; cong; sym; trans; subst)
open PropEq.≡-Reasoning
open import Function using (_∘_; id; flip; _$_)

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


