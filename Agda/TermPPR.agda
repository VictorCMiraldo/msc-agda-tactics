module TermPPR where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; filter; length) renaming (_++_ to _⊹_)
open import Data.String using (String; _++_)
open import Data.Unit
open import Data.Product using (_×_; _,_) renaming (proj₁ to p1; proj₂ to p2)
open import Function using (_∘_)
open import Reflection

-----------------------------------------------------------
-- * State Monadic wrapper

record ST (s : Set)(a : Set) : Set1 where
  field
    unST : s → (a × s)

runST : ∀{a s} → ST s a → s → (a × s)
runST r = (ST.unST r)

evalST : ∀{a s} → ST s a → s → a
evalST r = p1 ∘ (runST r)

return : ∀{a s} → a → ST s a
return x = record { unST = λ s → (x , s) }

_>>=_ : ∀{a b s} → ST s a → (a → ST s b) → ST s b
x >>= f = record { unST = λ s →
                              let x′ : _
                                  x′ = runST x s
                              in  runST (f (p1 x′)) (p2 x′)
                 }

_>>_ : ∀{a b s} → ST s a → ST s b → ST s b
x >> f = x >>= λ _ → f

get : ∀{s} → ST s s
get = record { unST = λ s → (s , s) }

put : ∀{s} → s → ST s Unit
put x = record { unST = λ _ → (unit , x) }
 
modify : ∀{s} → (s → s) → ST s Unit
modify f = record { unST = λ s → (unit , f s) }

----------------------------------------------------------------
-- Testing our State Monad

open import Data.Fin using (Fin; fromℕ≤) renaming (zero to fzero; suc to fsuc)
open import Data.Vec using (Vec; lookup)
open import Data.Nat as N using (ℕ; zero; suc; _+_; _≤?_;
                                 _≤_; z≤n; s≤s) renaming (_≟_ to _≟N_; _<_ to _N<_)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Core
open import Relation.Binary using (Decidable)

postulate 
  error : ∀{a}{A : Set a} → String → A
  notimp : ∀{a}{A : Set a} → A

-- We'll store a vector of names to pretty-print variables.
record PPRData (n : ℕ) : Set where
  field
    pprData  : Vec String n
    pprLevel : ℕ

data Either (A B : Set) : Set where
  inl : A → Either A B
  inr : B → Either A B

NameStr : Set
NameStr = List (Either Name String)

n[_] : Name → NameStr
n[ nm ] = (inl nm) ∷ []

s[_] : String → NameStr
s[ str ]  = (inr str) ∷ []

-- We need to fetch the ids.
getId : ∀{n} → Fin n → PPRData n → NameStr
getId f v = s[ lookup f (PPRData.pprData v) ]

-- Or increase the level
lvlF : ∀{n} → (ℕ → ℕ) → PPRData n → PPRData n
lvlF f p = record { pprData = PPRData.pprData p
                  ; pprLevel = f (PPRData.pprLevel p) 
                  }

lvlUp : ∀{n} → PPRData n → PPRData n
lvlUp = lvlF suc

-- State monad wrapping.
getIdSt : ∀{n} → Fin n → ST (PPRData n) NameStr
getIdSt f = get >>= \s → return (getId f s) 

-- We might need to translate a nat to a fin.
embed : ∀{m} → ℕ → Fin m
embed {m} n with n N.≤? m
...| yes f = embed′ f
           where
             embed′ : ∀{m n} → m N.≤ n → Fin n
             embed′ {n = zero} z≤n     = error "Out of scope"
             embed′ {zero} {suc n} z≤n = fzero
             embed′ (s≤s p)            = fsuc (embed′ p)
...| no _  = error "Out of scope"

getIdStℕ : ∀{n} → ℕ → ST (PPRData n) NameStr
getIdStℕ n = getIdSt (embed n)

------------------
-- Pretty Printing
------------------

pprT : ∀{n} → Term → ST (PPRData n) NameStr
pprA : ∀{n} → Arg Term → ST (PPRData n) NameStr
pprAL : ∀{n} → List (Arg Term) → ST (PPRData n) NameStr

pprT (var x args) = getIdStℕ x >>=
                      (λ r → pprAL args >>= (λ l → return (r ⊹ l)))
pprT (con c args) = pprAL args >>= (λ l → return (n[ c ] ⊹ l))
pprT (def f args) = pprAL args >>= (λ l → return (n[ f ] ⊹ l))
pprT (lam v t) = {!!}
pprT (pat-lam cs args) = {!!}
pprT (pi t₁ t₂) = {!!}
pprT (sort x) = {!!}
pprT (lit x) = {!!}
pprT unknown = {!!}


pprA t = {!!}


pprAL l = {!!}

{-
fetchId′ : ℕ → PPRData → String
fetchId′ i r = let l' = filter (λ x → toBool (x ≟N i)) (PPRData.nms r)
               in ?
-}
uniqueId : ST ℕ ℕ
uniqueId = get >>= (λ y → put (y + 1) >> return y)

termPPR : Term → String
termPPR = {!!} 
