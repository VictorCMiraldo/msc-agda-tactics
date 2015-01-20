open import Prelude
open import Data.Nat using (_≤_; z≤n; s≤s)

module RWUtils where

  -- compute the difference between two natural numbers, given an
  -- ordering between them.
  Δ_ : ∀ {m n} → m ≤ n → ℕ
  Δ z≤n {k} = k
  Δ s≤s  p  = Δ p

  -- correctness proof of the difference operator Δ.
  Δ-correct : ∀ {m n} (p : m ≤ n) → n ≡ m + Δ p
  Δ-correct  z≤n    = refl
  Δ-correct (s≤s p) = cong suc (Δ-correct p)

  _-Δ-_ : ∀{m}(n : ℕ)(p : m ≤ n) → ℕ 
  n       -Δ- z≤n     = n
  (suc n) -Δ- s≤s prf = n -Δ- prf
