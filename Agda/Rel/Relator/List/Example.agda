open import Prelude hiding (_*_; _+_) renaming (either to +-elim)

open import Rel.Core
open import Rel.Core.Coproduct
open import Rel.Core.Product
open import Rel.Core.Equality

open import Rel.Relator
open import Rel.Relator.List
open import Rel.Relator.List.Defs
open import Rel.Relator.List.Instances


module Rel.Relator.List.Example where

  open Composes {{...}}
  open IsDec    {{...}}
  
  l1 : Lw ℕ
  l1 = cons (1 , cons (2 , nil))

  l2 : Lw ℕ
  l2 = cons (1 , cons (2 , cons (3 , nil)))

  l3 : Lw ℕ
  l3 = cons (4 , nil)

  prefix-gene : Rel (L ℕ (Lw ℕ)) (Lw ℕ)
  prefix-gene = either nilR (nilR ∪ consR)

  prefix : Rel (Lw ℕ) (Lw ℕ)
  prefix = ⟦ prefix-gene ⟧₁

  prf1 : {{ i : IsDec prefix }} → Dec (prefix l1 l3)
  prf1 {{ dec i }} = i l1 l3
