open import Prelude
open import Data.Maybe using (Maybe; just; nothing)
open import Reflection renaming (Term to AgTerm; Type to AgType)
open import RTerm
open import RTermUtils
open import Unification

open import Rel.Core.Equality

module RW where

  open import Monads
  open Monad {{...}}

  {-
  rw-≡r : RTerm (Maybe ℕ) → Maybe (RTerm ℕ) → RSubst → RTerm ℕ
  rw-≡r g□ action σ = {!!}

  rw-≡ : RTerm (Maybe ℕ) → Maybe (RTerm ℕ) → RSubst → RTerm ℕ
  rw-≡ g□ action σ = {!!}
  -}

  pattern pat-≡  = (rdef (quote _≡_))
  pattern pat-≡r = (rdef (quote _≡r_))
  pattern pat-→  = impl

  makeApp : Name → RSubst → RTerm ℕ
  makeApp act σ = rapp (rdef act) (map p2 σ)

  selectStrat : RTermName → RTermName -- We need both heads to decide what to do
              → RTerm (Maybe ℕ)       -- A term with a hole, or our abs.
              → Name                  -- Action name.
              → RSubst                -- Unification result.
              → RTerm ℕ
  selectStrat pat-≡ pat-≡ g□ act σ
    {- = rapp (rdef (quote cong))
           ( hole2Abs g□
           ∷ makeApp act σ
           ∷ [])
    -}
    = rapp (rdef (quote subst)) 
           ( hole2Abs g□ 
           ∷ makeApp act σ 
           ∷ rapp (rcon (quote refl)) [] 
           ∷ [])
  -- selectStrat pat-→ pat-≡r g□ act σ
  --  = {!!}
  selectStrat _ _ _ _ _
    = error "Not yet implemented"

  RW+1 : Name → AgTerm → Maybe AgTerm
  RW+1 act goal with Ag2RTerm goal | Ag2RType (type act)
  ...| g' | ty with forceBinary g' | (typeResult ty) >>= forceBinary
  ...| just (hdₓ , g1 , g2) | just (hdₐ , ty1 , ty2)
    = let g□ = g1 ∩↑ g2
          u1 = (g□ -↓ g1) >>= (unify ty1)
          u2 = (g□ -↓ g2) >>= (unify ty2)
          σ  = μ ((_++ᵣ_ <$> u1) <*> u2)
      in (R2AgTerm ∘ selectStrat hdₓ hdₐ g□ act) <$> σ
      where
        μ : ∀{a}{A : Set a} → Maybe (Maybe A) → Maybe A
        μ (just x) = x
        μ nothing  = nothing
  ...| _ | _ = error "[RW+1] Somewthing went wrong."

  RW : Name → AgTerm → AgTerm
  RW act goal with RW+1 act goal
  ...| just t  = t
  ...| nothing = error "[RW] Something went wrong."
