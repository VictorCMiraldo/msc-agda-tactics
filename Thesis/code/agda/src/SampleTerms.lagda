\begin{code}
open import Prelude hiding (_+_; _*_) renaming (either to +-elim)
open import RW.Language.RTerm
open import RW.Language.RTermUtils
open import Rel.Core
open import Rel.Core.Coproduct
open import Rel.Core.Equality
-- open import Rel.Properties.BiFunctor
\end{code}

%<*sample-type-1>
\begin{code}
+-ᵒ-distr : {A B C D : Set}{R : Rel A B}{S : Rel C D}
          → (R ᵒ + S ᵒ) ≡r (R + S) ᵒ
\end{code}
%</sample-type-1>
\begin{code}
+-ᵒ-distr = ?
\end{code}

%<*sample-term-1>
\begin{code}
+-ᵒ-distr-size : S (Ag2RType (type (quote +-ᵒ-distr))) ≡ 22
+-ᵒ-distr-size = refl
\end{code}
%</sample-term-1>
\begin{code}
  where open import Rel.Properties.BiFunctor
\end{code}
