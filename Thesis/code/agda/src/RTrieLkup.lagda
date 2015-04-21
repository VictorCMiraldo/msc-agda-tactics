\begin{code}
open import Prelude

open import Level using (_⊔_; Lift; lift) renaming (suc to ls; zero to lz)
open import Data.String using (String)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Nat using (_≤_)

open import RW.Data.RTrie.Decl

open import RW.Utils.Monads
open Monad {{...}}
open Eq {{...}}
  
import RW.Data.PMap (RTermᵢ ⊥) as IdxMap
import RW.Data.PMap ℕ as ℕmap
\end{code}

%<*label-lst-def>
\begin{code}
Label : Set
Label = ℕ ⊎ Name

Lst : Set
Lst = ℕmap.to (RTerm ⊥) × Maybe Label
\end{code}
%</label-lst-def>

\begin{code}
Lst-empty : Lst
Lst-empty = ℕmap.empty , nothing

Lst-open : Lst → (ℕmap.to (RTerm ⊥) × Maybe Name)
Lst-open (e , l) = (e , lbl-join l)
  where
    lbl-join : Maybe Label → Maybe Name
    lbl-join nothing = nothing
    lbl-join (just (i1 _)) = nothing
    lbl-join (just (i2 a)) = just a
\end{code}

%<*L-monad>
\begin{code}
L : Set → Set
L = Reader (List Lst)
\end{code}
%</L-monad>

\begin{code}
applyBRule1 : Rule → Lst → Lst
applyBRule1 (Gr x)   (e , _) = e , just (i1 x)
applyBRule1 (Tr x y) (e , just (i1 l)) 
  with x ≟-ℕ l
...| yes _ = e , just (i1 y)
...| no  _ = e , nothing
applyBRule1 (Tr x y) (e , just (i2 _)) = e , nothing
applyBRule1 (Fr x y) (e , just (i1 l))
  with x ≟-ℕ l
...| yes _ = e , just (i2 y)
...| no  _ = e , nothing
applyBRule1 (Fr _ _) (e , just (i2 _)) = e , nothing
applyBRule1 _        (e , nothing) = e , nothing

applyBRule : Rule → L (List Lst)
applyBRule r = reader-ask >>= return ∘ (Prelude.map (applyBRule1 r))
\end{code}

%<*ruleList-type>
\begin{code}
ruleList : List Rule → L (List Lst)
\end{code}
%</ruleList-type>
\begin{code}
ruleList = ?

map-filter : ∀{a}{A B : Set a} → (B → Bool) → (A → B) → List A → List B
map-filter p f = foldr (λ h r → let x = f h in ite (p x) (x ∷ r) r) []
  where
    ite : ∀{a}{A : Set a} → Bool → A → A → A
    ite true  t _ = t
    ite false _ e = e
\end{code}

%<*lkup-inst1-type>
\begin{code}
lkup-inst1 : RTerm ⊥ → ℕ × List Rule → L (List Lst)
\end{code}
%</lkup-inst1-type>
\begin{code}
lkup-inst1 = ?
\end{code}

%<*lkup-inst-type>
\begin{code}
lkup-inst : RTerm ⊥ → List (ℕ × List Rule) → L (List Lst)
\end{code}
%</lkup-inst-type>
\begin{code}
lkup-inst = ?
\end{code}

%<*lkup-list-type>
\begin{code}
lkup-list : List (RTerm ⊥ × Cell) → L (List Lst)
\end{code}
%</lkup-list-type>
\begin{code}
lkup-list = ?
\end{code}

%<*lkup-aux-def>
\begin{code}
lkup-aux : RTerm ⊥ → RTrie → L (List Lst)
lkup-aux _ (Leaf r) = ruleList r
lkup-aux k (Fork (((d , rs) , bs) ∷ [])) 
  = let tid , tr = out k
  in lkup-inst k bs
  >>= λ r → maybe (lkup≡just tr) (lkup-aux k d) (IdxMap.lkup tid rs)
  >>= return ∘ (_++_ r)
  where
    lkup≡just : List (RTerm ⊥) → RTrie → L (List Lst)
    lkup≡just [] (Leaf r) = ruleList r
    lkup≡just _  (Leaf _) = return []
    lkup≡just tr (Fork ms) = lkup-list (zip tr ms)
\end{code}
%</lkup-aux-def>
\begin{code}
lkup-aux _ _ = ?
\end{code}

%<*lkup-type>
\begin{code}
lookup : RTerm ⊥ → RTrie → List (ℕmap.to (RTerm ⊥) × Name)
\end{code}
%</lkup-type>
\begin{code}
lookup = ?
\end{code}



