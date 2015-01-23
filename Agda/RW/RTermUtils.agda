open import Prelude
open import RTerm
open import Data.Maybe using (Maybe; just; nothing; is-just)
open import Reflection using (_≟-Lit_; _≟-Name_)
open import Monads

module RTermUtils where

  open Monad {{...}}

  -------------------------------------------------------
  -- Terms with Context
  --
  --   Holes will be represented by a nothing;
  pattern hole = ovar nothing

  isHole : ∀{A} → RTerm (Maybe A) → Bool
  isHole (ovar nothing) = true
  isHole _              = false

  -- Term Intersection
  --
  {-# TERMINATING #-}
  _∩_ : ∀{A} ⦃ eqA : Eq A ⦄ 
      → RTerm A → RTerm A → RTerm (Maybe A)
  _∩_ (rapp x ax) (rapp y ay) with x ≟-RTermName y
  ...| no  _ = ovar nothing
  ...| yes _ = rapp x (map (uncurry _∩_) (zip ax ay))
  _∩_ (ivar x) (ivar y) with x ≟-ℕ y
  ...| no  _ = ovar nothing
  ...| yes _ = ivar x
  _∩_ ⦃ eq f ⦄ (ovar x) (ovar y) with f x y
  ...| no  _ = ovar nothing
  ...| yes _ = ovar (just x)
  _∩_ (rlit x) (rlit y) with x ≟-Lit y
  ...| no  _ = ovar nothing
  ...| yes _ = rlit x
  _∩_ (rlam x) (rlam y) = x ∩ y
  _∩_ _ _ = ovar nothing

  -- Lifting holes.
  --
  --  Will translate every definition with only holes as arguments
  --  into a single hole.
  {-# TERMINATING #-}
  _↑ : ∀{A} → RTerm (Maybe A) → RTerm (Maybe A)
  _↑ (rapp x ax) with all isHole ax
  ...| true   = ovar nothing
  ...| false  = rapp x (map _↑ ax)
  _↑ (rlam x) = rlam (x ↑)
  _↑ t        = t

  -- It is commom to need only "linear" intersections;
  _∩↑_ : ∀{A} ⦃ eqA : Eq A ⦄ 
       → RTerm A → RTerm A → RTerm (Maybe A)
  v ∩↑ u = (v ∩ u) ↑

  -- Term Subtraction
  {-# TERMINATING #-}
  _-_ : ∀{A} ⦃ eqA : Eq A ⦄ → RTerm (Maybe A) → RTerm A → Maybe (List (RTerm A))
  hole - t = return (t ∷ [])
  (rapp x ax) - (rapp y ay) with x ≟-RTermName y
  ...| no  _ = nothing
  ...| yes _ = joinInner (map (uncurry _-_) (zip ax ay))
     where
       joinInner : ∀{A} → List (Maybe (List A)) → Maybe (List A)
       joinInner [] = return []
       joinInner (nothing ∷ _) = nothing
       joinInner (just x ∷ xs) = joinInner xs >>= return ∘ _++_ x
  (rlam x) - (rlam y) = x - y
  x - y with x ≟-RTerm (replace-A (ovar ∘ just) y)
  ...| yes _ = just []
  ...| no  _ = nothing
