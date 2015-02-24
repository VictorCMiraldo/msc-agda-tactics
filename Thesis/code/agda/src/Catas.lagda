\begin{code}
open import Prelude
open import Rel.Core
open import Rel.Core.Equality
\end{code}

%<*wtype-def>
\begin{code}
data W (S : Set)(P : S → Set) : Set where
  sup : (s : S) → (P s → W S P) → W S P
\end{code}
%</wtype-def>

\begin{code}
{-# TERMINATING #-}
\end{code}
%<*w-elim>
\begin{code}
W-rec : ∀{c}{S : Set}{P : S → Set}
     → (C : W S P → Set c)
     → (c : (s : S)  
          → (f : P s → W S P) 
          → (h : (p : P s) → C (f p)) 
          → C (sup s f)) 
     → (x : W S P) → C x 
W-rec C c (sup s f) = c s f (W-rec C c ∘ f)
\end{code}
%</w-elim>
