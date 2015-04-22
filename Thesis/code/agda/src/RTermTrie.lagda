\begin{code}
open import Prelude
open import RW.Language.RTerm
open import RW.Language.RTermUtils
open import RW.Language.RTermIdx
open import RW.Data.RTrie

open import RW.Strategy using (Trs; Symmetry; UData; u-data)
\end{code}

%<*add-action-def>
\begin{code}
add-action : Name → ℕ × RTrie → ℕ × RTrie
add-action act bt
  = let
    ty = lift-ivar $ typeResult $ Ag2RType $ type act
  in insertTerm act ty bt
\end{code}
%</add-action-def>

\begin{code}
replicateM : {A : Set} → List (Maybe A) → Maybe (List A)
replicateM [] = just []
replicateM (nothing ∷ _)  = nothing
replicateM (just x  ∷ xs) with replicateM xs
...| just xs' = just (x ∷ xs')
...| nothing  = nothing
\end{code}

%<*search-action-def>
\begin{code}
search-action : RTermName → RBinApp ⊥ → RTrie → List (Name × UData)
search-action hd (_ , g₁ , g₂) trie 
  = let g□ = g₁ ∩↑ g₂
        u₁ = g□ -↓ g₁
        u₂ = g□ -↓ g₂
        ul = replicateM (u₁ ∷ u₂ ∷ [])
  in maybe (mkSearch g□) (ul-is-nothing ∷ []) ul
\end{code}
%</search-action-def>
\begin{code}
  where
    postulate ul-is-nothing : Name × UData
    postulate mkSearch : RTerm (Maybe ⊥) → List (RTerm ⊥) → List (Name × UData)
\end{code}
