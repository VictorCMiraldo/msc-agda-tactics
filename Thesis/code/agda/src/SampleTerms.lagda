\begin{code}
open import Prelude hiding (_+_; _*_) renaming (either to +-elim)
open import RW.Language.RTerm
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
+-ᵒ-distr-term : RTerm ⊥
+-ᵒ-distr-term = rapp (rdef (quote _≡r_))
  (rapp (rdef (quote either))
   (rapp (rdef (quote _∙_))
    (rapp (rdef (quote fun)) (rapp (rcon (quote i1)) [] ∷ []) ∷
     rapp (rdef (quote _ᵒ)) (ivar 1 ∷ []) ∷ [])
    ∷
    rapp (rdef (quote _∙_))
    (rapp (rdef (quote fun)) (rapp (rcon (quote i2)) [] ∷ []) ∷
     rapp (rdef (quote _ᵒ)) (ivar 0 ∷ []) ∷ [])
    ∷ [])
   ∷
   rapp (rdef (quote _ᵒ))
   (rapp (rdef (quote either))
    (rapp (rdef (quote _∙_))
     (rapp (rdef (quote fun)) (rapp (rcon (quote i1)) [] ∷ []) ∷
      ivar 1 ∷ [])
     ∷
     rapp (rdef (quote _∙_))
     (rapp (rdef (quote fun)) (rapp (rcon (quote i2)) [] ∷ []) ∷
      ivar 0 ∷ [])
     ∷ [])
    ∷ [])
   ∷ [])
\end{code}
%</sample-term-1>
