open import Prelude
open import Data.Maybe using (Maybe; just; nothing)

open import RW.Language.RTerm
open import RW.Language.RTermUtils using (hole2Absℕ)
open import RW.Language.Unification using (RSubst)
open import RW.Utils.Error
open import RW.Strategy

open import Rel.Core.Equality

module Rel.Reasoning.RelEq-Strategy where

  pattern pat-≡r = (rdef (quote _≡r_))
  pattern pat-→  = impl

  private
    rel-when : RTermName → RTermName → Bool
    rel-when pat-→ pat-≡r = true
    rel-when _     _      = false

    fixTrs : Trs → RTerm ℕ → RTerm ℕ
    fixTrs Symmetry term = rapp (rdef (quote ≡r-sym)) (term ∷ [])

    rel-how : Name → UData → Err StratErr (RTerm ℕ)
    rel-how act (u-data g□ σ trs) = i2 (
      rapp (rdef (quote subst)) 
           ( hole2Absℕ g□
           ∷ rapp (rdef (quote ≡r-promote)) 
                  (foldr fixTrs (makeApp act σ) trs ∷ [])
           ∷ []))

  rel-strat : TStrat
  rel-strat = record
    { when = rel-when
    ; how  = rel-how
    }
