\begin{code}
open import Prelude

open import Level using (_⊔_; Lift; lift) renaming (suc to ls; zero to lz)
open import Data.String using (String)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Nat using (_≤_)

open import Relation.Binary.PropositionalEquality
  using (inspect; [_])

open import RW.Data.RTrie.Decl
import RW.Data.PMap (RTermᵢ ⊥) as IdxMap
import RW.Data.PMap ℕ as ℕmap

postulate 
  trie-err : ∀{a}{A : Set a} → String → A 

open import RW.Utils.Monads
open Monad {{...}}
open Eq {{...}}
\end{code}

%<*I-monad>
\begin{code}
I : ∀{a} → Set a → Set a
I {a} = STₐ {lz} {a} (Σ ℕ (λ _ → Maybe ℕ)) 
\end{code}
%</I-monad>

%<*CellCtx-decl>
\begin{code}
CellCtx : Set _
CellCtx = RTrie → Cell
\end{code}
%</CellCtx-decl>

\begin{code}
_<$>_ : ∀{a}{A B : Set a} → (A → B) → I A → I B
f <$> ix = ix >>= (return ∘ f)

private
  getLbl : I (Maybe ℕ)
  getLbl = getₐ >>= return ∘ p2

  putLbl : ℕ → I Unit
  putLbl n = getₐ >>= λ x → putₐ (p1 x , just n)

  getCount : I ℕ
  getCount = p1 <$> getₐ

  putCount : ℕ → I Unit
  putCount x = getLbl >>= putₐ ∘ (_,_ x)

  ++count : I ℕ
  ++count = getCount <>= (putCount ∘ suc)

  singleton : ∀{a}{A : Set a} → A → List A
  singleton x = x ∷ []
  
applyBRule : Rule → ℕ → Maybe ℕ
applyBRule (Tr m n) k with m ≟-ℕ k
...| yes _ = just n
...| no  _ = nothing
applyBRule _ _ = nothing
\end{code}

%<*makeRule-def>
\begin{code}
makeRule : I Rule
makeRule = getLbl
       >>= λ l → (++count <>= putLbl) 
       >>= λ c′ → return $ maybe (flip Tr c′) (Gr c′) l
\end{code}
%</makeRule-def>

%<*handleRules-def>
\begin{code}
handleRules : List Rule → I (List Rule)
handleRules rs = getLbl >>= maybe (flip l≡just rs) (l≡nothing rs)
  where
    l≡just : ℕ → List Rule → I (List Rule)
    l≡just l [] = singleton <$> makeRule
    l≡just l (r ∷ rs) with applyBRule r l
    ...| just l′ = putLbl l′ >> return (r ∷ rs)
    ...| nothing = (_∷_ r) <$> l≡just l rs

    l≡nothing : List Rule → I (List Rule)
    l≡nothing [] = singleton <$> makeRule
    l≡nothing ((Gr k) ∷ rs) = putLbl k >> return ((Gr k) ∷ rs)
    l≡nothing (r ∷ rs)      = _∷_ r <$> l≡nothing rs
\end{code}
%</handleRules-def>

%<*mIdx-def>
\begin{code}
mIdx : Cell → RTermᵢ ⊥ 
     → I (CellCtx × RTrie)
mIdx ((d , mh) , bs) (ivarᵢ _)
  = return $ (λ bt → (merge d bt , mh) , bs) , BTrieEmpty
  where
    merge : RTrie → RTrie → RTrie
    merge (Leaf as) (Leaf bs) = Leaf (as ++ bs)
    merge _ bt                = bt 
mIdx ((d , mh) , bs) tid
  = let mh′ , prf = IdxMap.alterPrf BTrieEmpty tid mh
  in return $ (λ f → (d , IdxMap.insert tid f mh) , bs) 
            , (IdxMap.lkup' tid mh′ prf)
\end{code}
%</mIdx-def>

%<*mSym-def>
\begin{code}
mSym : Cell → ℕ
     → I (CellCtx × RTrie)
mSym (mh , bs) tsym with ℕmap.lkup tsym bs
...| nothing = makeRule
           >>= λ r → return (const (mh , (tsym , r ∷ []) ∷ bs) 
                            , BTrieEmpty)
...| just rs = handleRules rs
           >>= λ r → return (const (mh , ℕmap.insert tsym r bs) 
                            , BTrieEmpty)
\end{code}
%</mSym-def>

%<*M-def>
\begin{code}
𝑴 : {A : Set}{{enA : Enum A}} 
   → Cell → RTermᵢ A → I (CellCtx × RTrie)
𝑴 {{enum aℕ _}} c tid with toSymbol tid | inspect toSymbol tid
...| nothing | [ prf ] = mIdx c (idx-cast tid prf)
...| just s  | _       = maybe (mSym c) enum-err (aℕ s)
  where postulate enum-err : I (CellCtx × RTrie)
\end{code}
%</M-def>

\begin{code}
insCell* : {A : Set}{{enA : Enum A}} 
         → List (RTerm A) → List Cell → I (List Cell)
insCell* = ?

insCell*ε : {A : Set}{{enA : Enum A}} → List (RTerm A) → I (List Cell)
insCell*ε = ?
\end{code}

%<*insert-def>
\begin{code}
{-# TERMINATING #-}
insCell : {A : Set}{{enA : Enum A}} 
        → RTermᵢ A × List (RTerm A) → Cell → I Cell
insCell (tid , tr) cell
  = 𝑴 cell tid
  >>= λ { (c , bt) → insCellAux tid tr bt >>= return ∘ c }
  where
    tr≡[] : {A : Set}{{enA : Enum A}} 
          → RTermᵢ A → I RTrie
    tr≡[] tid with toSymbol tid
    ...| nothing = (Leaf ∘ singleton) <$> makeRule
    ...| _       = return $ Fork []

    insCellAux : {A : Set}{{enA : Enum A}} 
               → RTermᵢ A → List (RTerm A) → RTrie 
               → I RTrie
    insCellAux tid _  (Leaf r) = return (Leaf r)
    insCellAux tid [] _        = tr≡[] tid
    insCellAux tid tr (Fork []) 
      = Fork <$> insCell*ε tr
    insCellAux tid tr (Fork ms)
      = Fork <$> insCell* tr ms
\end{code}
%</insert-def>
