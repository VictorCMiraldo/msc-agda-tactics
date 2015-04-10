open import Level using (Level)
open import Function using (_∘_; id; flip)
open import Data.Fin as Fin using (Fin; fromℕ) renaming (zero to fz; suc to fs)
open import Data.Nat as Nat using (ℕ; suc; zero; _+_; _⊔_; decTotalOrder; _<_; _≤_; s≤s; z≤n) renaming (_≟_ to _≟-ℕ_)
open import Data.Nat.Properties.Simple using (+-comm; +-right-identity; +-assoc)
open import Data.Nat.Properties as ℕ-Props
open import Data.Nat.Show using (show)
open import Data.String as Str renaming (_++_ to _++s_)
open import Data.Char using (Char)
open import Data.List as List using (List; []; _∷_; [_]; concatMap; _++_; length; map)
open import Data.Vec as Vec using (Vec; []; _∷_; _∷ʳ_; reverse; initLast; toList)
open import Data.Product as Prod using (∃; _×_; _,_; proj₁; proj₂; uncurry)
open import Data.Maybe as Maybe using (Maybe; just; nothing; maybe)
open import Data.Sum as Sum using (_⊎_; inj₁; inj₂)
open import Data.Integer as Int using (ℤ; -[1+_]; +_) renaming (_≟_ to _≟-Int_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary using (module DecTotalOrder)
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_; refl; cong; sym; subst)
open import Reflection renaming (Term to AgTerm; _≟_ to _≟-AgTerm_)
open import Algebra using (module CommutativeSemiring; module DistributiveLattice)

open import RW.Language.RTerm
open import RW.Language.RTermUtils
open import RW.Language.Instantiation

open import Relation.Binary.PropositionalEquality

open import Rel.Reasoning.RelEq-Strategy
open import RW.Strategy.PropEq

open import RW.RW (≡-strat ∷ rel-⊆-strat ∷ [])

module RWTestingTrans where

  open ≡-Reasoning

  -- This is pretty slow...
  test2 : (x y : ℕ) → (x + y) + 0 ≡ y + (x + 0)
  test2 x y
    = begin
      (x + y) + 0
    ≡⟨ (tactic (by*-≡ (quote +-comm ∷ quote +-assoc ∷ []))) ⟩
      y + (x + 0)
    ∎

  {- 

  Using a max height of 2 in the goal guesser.

  Finished RWTestingTrans.
  46,981,963,256 bytes allocated in the heap
   7,318,699,728 bytes copied during GC
     387,537,960 bytes maximum residency (20 sample(s))
       8,253,392 bytes maximum slop
            1042 MB total memory in use (0 MB lost due to fragmentation)

                                    Tot time (elapsed)  Avg pause  Max pause
  Gen  0     90092 colls,     0 par   17.25s   17.25s     0.0002s    0.0030s
  Gen  1        20 colls,     0 par    5.15s    5.17s     0.2587s    0.6522s

  INIT    time    0.00s  (  0.00s elapsed)
  MUT     time  241.64s  (241.88s elapsed)
  GC      time   22.40s  ( 22.42s elapsed)
  EXIT    time    0.09s  (  0.09s elapsed)
  Total   time  264.12s  (264.40s elapsed)

  %GC     time       8.5%  (8.5% elapsed)

  Alloc rate    194,432,035 bytes per MUT second

  Productivity  91.5% of total user, 91.4% of total elapsed

  -}
  {-

  Using a height of 1

  Finished RWTestingTrans.
  31,222,657,544 bytes allocated in the heap
   5,109,928,984 bytes copied during GC
     355,162,768 bytes maximum residency (18 sample(s))
       7,579,240 bytes maximum slop
             952 MB total memory in use (0 MB lost due to fragmentation)

                                    Tot time (elapsed)  Avg pause  Max pause
  Gen  0     59723 colls,     0 par   12.21s   12.22s     0.0002s    0.0036s
  Gen  1        18 colls,     0 par    3.91s    3.92s     0.2179s    0.6516s

  INIT    time    0.00s  (  0.00s elapsed)
  MUT     time  154.42s  (154.57s elapsed)
  GC      time   16.12s  ( 16.14s elapsed)
  EXIT    time    0.09s  (  0.09s elapsed)
  Total   time  170.63s  (170.80s elapsed)

  %GC     time       9.5%  (9.5% elapsed)

  Alloc rate    202,197,812 bytes per MUT second

  Productivity  90.5% of total user, 90.5% of total elapsed

  -}
