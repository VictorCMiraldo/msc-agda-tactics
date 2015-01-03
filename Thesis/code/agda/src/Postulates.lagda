%<*function-extensionality>
\begin{code}
postulate
  func-ext : {A : Set} {B : A → Set} {f g : (x : A) → B x} →
             (∀ x → f x ≡ g x) → f ≡ g
\end{code}    
%</function-extensionality>
