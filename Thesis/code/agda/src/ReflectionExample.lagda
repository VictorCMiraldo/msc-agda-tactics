\begin{code}
open import Reflection
open import Data.Nat
open import Relation.Binary.PropositionalEquality
open import Data.List
\end{code}

%<*example>
\begin{code}
example : quoteTerm (λ x → suc x) ≡ con (quote suc) []
example = refl
\end{code}
%</example>
