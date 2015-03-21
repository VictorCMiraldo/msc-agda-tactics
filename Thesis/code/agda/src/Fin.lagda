\begin{code}
open import Data.Nat
\end{code}

%<*fin-def>
\begin{code}
data Fin : ℕ → Set where
  fz : {n : ℕ} → Fin (suc n)
  fs : {n : ℕ} → Fin n → Fin (suc n)
\end{code}
%</fin-def>
