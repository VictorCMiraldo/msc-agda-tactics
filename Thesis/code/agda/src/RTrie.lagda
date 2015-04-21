\begin{code}
open import Prelude
open import RW.Language.RTerm
\end{code}

%<*istrie-def>
\begin{code}
record IsTrie (t : Set) : Set1 where
  field
    Idx : Set
    idx≡ : Eq Idx

    toSym   : Idx → Maybe ℕ 
    fromSym : ℕ   → Maybe Idx

    inₜ   : Idx × (List t) → t
    outₜ  : t → Idx × (List t)
\end{code}
%</istrie-def>

%<*rterm-idx-data>
\begin{code}
data RTermᵢ {a}(A : Set a) : Set a where
  ovarᵢ : (x : A) → RTermᵢ A
  ivarᵢ : (n : ℕ) → RTermᵢ A
  rlitᵢ : (l : Literal) → RTermᵢ A
  rlamᵢ : RTermᵢ A
  rappᵢ : (n : RTermName) → RTermᵢ A
\end{code}
%</rterm-idx-data>

\begin{code}
open import RW.Data.PMap (RTermᵢ ⊥) as IdxMap

postulate
  vv : Eq (RTermᵢ ⊥)
  
instance
  rtermi-eq : Eq (RTermᵢ ⊥)
  rtermi-eq = vv
\end{code}

%<*btrie-rule-def>
\begin{code}
data Rule : Set where
  Gr : ℕ     → Rule
  Tr : ℕ → ℕ → Rule
  Fr : ℕ → Name → Rule
\end{code}
%</btrie-rule-def>

%<*btrie-def>
\begin{code}
mutual
  Cell : Set
  Cell = IdxMap.to RTrie default 
       × List (ℕ × List Rule) 

  data RTrie : Set where
      Fork : List Cell → RTrie
      Leaf : List Rule → RTrie
\end{code}
%</btrie-def>

%<*rterm-idx-ops>
\begin{code}
out : ∀{a}{A : Set a} → RTerm A → RTermᵢ A × List (RTerm A)
out (ovar x)    = ovarᵢ x , []
out (ivar n)    = ivarᵢ n , []
out (rlit l)    = rlitᵢ l , []
out (rlam t)    = rlamᵢ , t ∷ []
out (rapp n ts) = rappᵢ n , ts

toSymbol : ∀{a}{A : Set a} → RTermᵢ A → Maybe A
toSymbol (ovarᵢ a) = just a
toSymbol _         = nothing

idx-cast : ∀{a b}{A : Set a}{B : Set b} 
         → (i : RTermᵢ A) → (toSymbol i ≡ nothing)
         → RTermᵢ B
idx-cast (ovarᵢ x) ()
idx-cast (ivarᵢ n) _ = ivarᵢ n
idx-cast (rlitᵢ l) _ = rlitᵢ l
idx-cast (rlamᵢ  ) _ = rlamᵢ
idx-cast (rappᵢ n) _ = rappᵢ n
\end{code}
%</rterm-idx-ops>
