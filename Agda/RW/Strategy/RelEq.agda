open import Prelude
open import Data.Maybe using (Maybe; just; nothing)

open import Language.RTerm
open import Language.RTermUtils using (hole2Abs)
open import Language.Unification using (RSubst)
open import Utils.Error
open import Strategy

open import Rel.Core.Equality

module Strategy.RelEq where

  pattern pat-≡r = (rdef (quote _≡r_))
  pattern pat-→  = impl

  private
    rel-when : RTermName → RTermName → Bool
    rel-when pat-→ pat-≡r = true
    rel-when _     _      = false

    rel-how : Name → RTerm (Maybe ℕ) → RSubst → Err StratErr (RTerm ℕ)
    rel-how act g□ σ = i2 (
      rapp (rdef (quote subst)) 
           ( hole2Abs g□
           ∷ rapp (rdef (quote ≡r-promote)) (makeApp act σ ∷ [])
           ∷ []))

  rel-strat : TStrat
  rel-strat = record
    { when = rel-when
    ; how  = rel-how
    }
