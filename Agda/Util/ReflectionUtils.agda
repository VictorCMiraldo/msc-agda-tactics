module Util.ReflectionUtils where

open import Data.Bool
open import Reflection
open import Data.Maybe using (Maybe; just; nothing; maybe)
open import Data.List using (List; []; _∷_; map)
open import Relation.Nullary.Decidable as Dec
open import Relation.Nullary using (Dec; yes; no)
open import Data.Nat using (ℕ; zero; suc)

-------------------------------------------------------------
-- * Arg

-- Predicates

argIsVisible : ∀{A} → Arg A → Bool
argIsVisible (arg (arg-info visible _) _) = true
argIsVisible _                            = false

-- Transformations

unArg : ∀{A} → Arg A → A
unArg (arg _ x) = x

mkArgVR : ∀{A} → A → Arg A
mkArgVR x = arg (arg-info visible relevant) x

-- Term Abstractions

{-# TERMINATING #-}
runAbstr1 : Term → Term → Maybe Term
runAbstr1 ta tb = abstrTerm ta tb
  where
    -- sums 1 to every DeBruijn index.
    mutual 
      shiftBy1 : Arg Term → Arg Term
      shiftBy1 (arg ai x) = arg ai (shiftTerm x)

      shiftArgs : List (Arg Term) → List (Arg Term)
      shiftArgs = Data.List.map shiftBy1 

      shiftTerm : Term → Term
      shiftTerm (var x args) = var (suc x) (shiftArgs args)
      shiftTerm (con c args) = con c (shiftArgs args)
      shiftTerm (def f args) = def f (shiftArgs args)
      shiftTerm t            = t -- TODO: how to correctly shift the rest? search some examples. 

    -- Given a list with holes, fill the holes with @t@. 
    fillHole : Term → List (Maybe (Arg Term)) → List (Arg Term)
    fillHole t = Data.List.map (maybe (λ x → x) (mkArgVR t))

    -- Will put 'nothing' where the list differs. Nothing represents a 'hole'.
    abstrArgL : List (Arg Term) → List (Arg Term) → List (Maybe (Arg Term))
    abstrArgL [] _ = []
    abstrArgL _ [] = []
    abstrArgL (a ∷ as) (b ∷ bs) with a ≟-ArgTerm b
    ...| yes _ = just (shiftBy1 a)  ∷ abstrArgL as bs
    ...| no  _ = nothing ∷ abstrArgL as bs

    -- given two terms, returns the common part of both terms.
    abstrTerm : Term → Term → Maybe Term
    abstrTerm (con a al) (con b bl) with a ≟-Name b
    ...| yes _ = just (lam visible (abs "l" (con a (fillHole (var 0 []) (abstrArgL al bl)))))
    ...| no  _ = nothing
    abstrTerm ta tb = nothing

    -- Will change the nothing for a 

termErase : Term → Term → Term
termErase = {!!}
