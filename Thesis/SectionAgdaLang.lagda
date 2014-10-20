Here we shall give a somewhat brief introduction to the agda language.
\begin{code}
  data Nat : Set where
    Zero : Nat
    Succ : Nat -> Nat
\end{code}
