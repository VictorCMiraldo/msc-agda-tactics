\begin{code}
open import Prelude
open import Data.Maybe using (Maybe; just; nothing) renaming (maybe′ to maybe)
open import Data.String

open import RW.Language.RTerm
open import RW.Language.RTermUtils
open import RW.Language.FinTerm
open import RW.Language.Instantiation

open import RW.Utils.Monads using (module Monad)
open import RW.Utils.Error
open Monad {{...}}
open IsError {{...}}

-- Strategy related errors
data StratErr : Set where
  Nothing       : StratErr
  NoUnification : StratErr
  NoUStrat      : StratErr
  NoTStrat      : StratErr
  Custom        : String → StratErr

instance
  IsError-StratErr : IsError StratErr
  IsError-StratErr = record { showError = showErr }
    where
      showErr : StratErr → String
      showErr Nothing       = "Nothing; Internal msg passing flag."
      showErr NoUnification = "No unification could be performed."
      showErr NoUStrat      = "No suitable unification strategy found."
      showErr NoTStrat      = "No suitable term stragety found."
      showErr (Custom msg)  = "[!] " Data.String.++ msg
\end{code}

%<*RWData-def>
\begin{code}
record RWData : Set where
  constructor rw-data
  field 
    goal   : RBinApp ⊥
    actℕ   : ℕ
    act    : RBinApp (Fin actℕ)
    ctx    : List (RTerm ⊥)
\end{code}
%</RWData-def>

%<*Trs-def>
\begin{code}
data Trs : Set where
  Symmetry : Trs
\end{code}
%</Trs-def>

%<*UData-def>
\begin{code}
record UData : Set where
  constructor u-data
  field
    □ : RTerm Unit
    σ : RSubst
    trs : List Trs
\end{code}
%</UData-def>

\begin{code}
private
  μ : ∀{a}{A : Set a} → Maybe (Maybe A) → Maybe A
  μ (just x) = x
  μ nothing  = nothing
\end{code}

%<*alternative-def>
\begin{code}
_<|>_ : ∀{a b}{A : Set a}{B E : Set b} ⦃ isErr : IsError E ⦄ 
      → (A → Err E B) → (A → Err E B)
      → A → Err E B
(f <|> g) a with f a
...| i1 _ = g a
...| i2b  = i2b
\end{code}
%</alternative-def>

%<*TStrat-def>
\begin{code}
record TStrat : Set where
  field
    when : RTermName → RTermName → Bool
    how  : Name → UData → Err StratErr (RTerm ⊥)
    
TStratDB : Set
TStratDB = List TStrat
\end{code}
%</TStrat-def>

%<*basic-def>
\begin{code}
basic : RWData → Err StratErr UData
basic (rw-data (hdₓ , g1 , g2) tn (hdₐ , ty1 , ty2)  _ )
  = let g□ = g1 ∩↑ g2
        u1 = (g□ -↓ g1) >>= (inst ty1)
        u2 = (g□ -↓ g2) >>= (inst ty2)
        σ  = μ ((_++ₓ_ <$> u1) <*> u2)
  in maybe (λ s → i2 (u-data (⊥2UnitCast g□) s [])) (i1 NoUnification) 
           (σ >>= X2RSubst)
\end{code}
%</basic-def>

\begin{code}
basic-sym : RWData → Err StratErr UData
basic-sym = ?
\end{code}

%<*runUStrats-def>
\begin{code}
runUStrats : RWData → Err StratErr UData
runUStrats = basic <|> basic-sym 
\end{code}
%</runUStrats-def>

\begin{code}
makeApp : Name → RSubst → RTerm ⊥
makeApp act σ = rapp (rdef act) (map p2 σ)
\end{code}

%<*strat-propeq>
\begin{code}
module PropEq where

  pattern pat-≡  = (rdef (quote _≡_))

  private
    open UData

    ≡-when : RTermName → RTermName → Bool
    ≡-when pat-≡ pat-≡ = true
    ≡-when _     _     = false

    fixTrs : Trs → RTerm ⊥ → RTerm ⊥
    fixTrs Symmetry term = rapp (rdef (quote sym)) (term ∷ [])

    ≡-how : Name → UData → Err StratErr (RTerm ⊥)
    ≡-how act (u-data g□ σ trs)
      = i2 (rapp (rdef (quote cong))
                 ( hole2Abs g□
                 ∷ foldr fixTrs (makeApp act σ) trs
                 ∷ [])
           )

  ≡-strat : TStrat
  ≡-strat = record
    { when = ≡-when
    ; how  = ≡-how
    }
\end{code}
%</strat-propeq>

