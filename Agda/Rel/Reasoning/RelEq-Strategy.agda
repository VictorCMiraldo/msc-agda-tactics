open import Prelude
open import Data.Maybe using (Maybe; just; nothing)

open import RW.Language.RTerm
open import RW.Language.RTermUtils using (hole2Abs)
open import RW.Language.Instantiation using (RSubst)
open import RW.Utils.Error
open import RW.Strategy

open import Rel.Core
open import Rel.Core.Equality

module Rel.Reasoning.RelEq-Strategy where

  pattern pat-≡r = (rdef (quote _≡r_))
  pattern pat-→  = impl

  private
    rel-⊆-when : RTermName → RTermName → Bool
    rel-⊆-when pat-→ pat-≡r = true
    rel-⊆-when _     _      = false

    rel-≡r-when : RTermName → RTermName → Bool
    rel-≡r-when pat-≡r pat-≡r = true
    rel-≡r-when _      _      = false

    fixTrs : Trs → RTerm ⊥ → RTerm ⊥
    fixTrs Symmetry term = rapp (rdef (quote ≡r-sym)) (term ∷ [])

    rel-⊆-how : Name → UData → Err StratErr (RTerm ⊥)
    rel-⊆-how act (u-data g□ σ trs) = i2 (
      rapp (rdef (quote subst)) 
           ( hole2Abs g□
           ∷ rapp (rdef (quote ≡r-promote)) 
                  (foldr fixTrs (makeApp act σ) trs ∷ [])
           ∷ []))

    rel-≡r-how : Name → UData → Err StratErr (RTerm ⊥)
    rel-≡r-how act (u-data (ovar unit) σ trs)
      = i2 (foldr fixTrs (makeApp act σ) trs)
    rel-≡r-how act (u-data g□ σ trs) = i2 (
      rapp (rdef (quote ≡r-cong))
           ( hole2Abs g□
           ∷ foldr fixTrs (makeApp act σ) trs
           ∷ []))

  rel-⊆-strat : TStrat
  rel-⊆-strat = record
    { when = rel-⊆-when
    ; how  = rel-⊆-how
    }

  rel-≡r-strat : TStrat
  rel-≡r-strat = record
    { when = rel-≡r-when
    ; how  = rel-≡r-how
    }

  open import RW.RW (rel-⊆-strat ∷ rel-≡r-strat ∷ [])
  
  by*-⊆ : by*-tactic 
  by*-⊆ = by* (quote ⊆-trans)

  by*-≡r : by*-tactic 
  by*-≡r = by* (quote ≡r-trans)
