open import Rel.Core
open import Rel.Core.Correflexive
open import Rel.Core.Equality
open import Rel.Reasoning.SubsetJudgement

open import Function using (id; _∘_; _$_)

open import Data.Unit using (Unit; unit)
open import Data.Empty using (⊥; ⊥-elim)

open import Data.List using (List; []; _∷_)

open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Nat.Properties.Simple
  using (+-suc; +-right-identity)

module Rel.CaseStudies.EvenTwice where

  ---------------------------------------------
  -- * Building Blocks

  twice : ℕ → ℕ
  twice zero    = zero
  twice (suc n) = suc (suc (twice n))

  twiceR : Rel ℕ ℕ
  twiceR = fun twice

  even : ℕ → Bool
  even zero          = true
  even (suc zero)    = false
  even (suc (suc n)) = even n

  So : Bool → Set
  So true  = Unit
  So false = ⊥

  evenR : Rel ℕ ℕ
  evenR = φ (So ∘ even)


  -----------------------------------------------
  -- * First we need to prove our assumption
  --   that (ρ twice ≡ even). This is somewhat
  --   complicated in agda. 
  --
  --   the proof follows:

  twiceIsN+N : (n : ℕ) → twice n ≡ n + n
  twiceIsN+N zero = refl
  twiceIsN+N (suc n) = cong suc (trans (cong suc (twiceIsN+N n)) (sym (+-suc n n)))

  twiceIsTwice : (n : ℕ) → twice n ≡ 2 * n
  twiceIsTwice zero = refl
  twiceIsTwice (suc n) rewrite +-right-identity n
    = cong suc (trans (cong suc (twiceIsN+N n)) (sym (+-suc n n))) 

  n*2-IsEven : (n : ℕ) → even (2 * n) ≡ true
  n*2-IsEven zero    = refl
  n*2-IsEven (suc n) 
    rewrite +-right-identity n
    | +-suc n n
      = subst (λ x → even (n + x) ≡ true) (+-right-identity n) (n*2-IsEven n)

  twiceEven : (a : ℕ) → even (twice a) ≡ true
  twiceEven zero = refl
  twiceEven (suc n) rewrite twiceIsTwice n = n*2-IsEven n

  div2 : (a : ℕ) → So (even a) → ℕ
  div2 zero _ = zero
  div2 (suc zero) ()
  div2 (suc (suc a)) so = suc (div2 a so)

  div2-twice-cancel : (b : ℕ) → (prf : So (even b))
                    → twice (div2 b prf) ≡ b
  div2-twice-cancel zero so = refl
  div2-twice-cancel (suc zero) ()
  div2-twice-cancel (suc (suc b)) so 
    = cong (λ x → suc (suc x)) (div2-twice-cancel b so)

  evenLemma1 : ρ twiceR ⊆ evenR
  evenLemma1 = ⊆in (λ b' b bTb 
    → let a = p1∙ (p1 (ρ.un bTb)) --  p1∙ (p1∩ bTb)
      in cons-φ $ p2 (ρ.un bTb) , evenLemma1Aux a b (fun.un $ p1 (p2∙ (p1 (ρ.un bTb))))
    ) where 
      evenLemma1Aux : (a : ℕ) → (b : ℕ) → twice a ≡ b → So (even b)
      evenLemma1Aux a b a*2≡b 
        rewrite sym a*2≡b
        | twiceEven a = unit

  evenLemma2 : evenR ⊆ ρ twiceR
  evenLemma2 = ⊆in (λ  b' b bEvena 
    → let evenb = p2 (φ.un bEvena)
          a , btwicea = evenLemma2Aux b evenb
      in cons-ρ ((a , (btwicea , (cons-ᵒ 
                    (cons-fun (subst (λ x → twice a ≡ x) (p1 $ φ.un bEvena) (fun.un btwicea)))))) 
                , (p1 $ φ.un bEvena))
    ) where
      evenLemma2Aux : (b : ℕ) → So (even b) 
                    → ∃ (λ x → twiceR b x)
      evenLemma2Aux b so with div2 b so | div2-twice-cancel b so
      evenLemma2Aux b so | a | prf with even b
      evenLemma2Aux b () | _ | prf | false 
      evenLemma2Aux b _  | a | prf | true = a , cons-fun prf

  -- Finally, our lemma.
  evenLemma : ρ twiceR ≡r evenR
  evenLemma = evenLemma1 , evenLemma2

  -------------------------------------------------------------
  -- * The actual equational proof that twice respects even.
  
  open import Rel.Reasoning.RelEq-Strategy using (rel-⊆-strat)
  open import RW.RW (rel-⊆-strat ∷ [])

  open import Rel.Properties.Basic
  open import Rel.Properties.Monotonicity
  open import Rel.Properties.Correflexive
  
  open import Rel.Properties.DatabaseList

  open ⊆-Reasoning

  twiceIsEven : (twiceR ∙ evenR ⊆ evenR ∙ twiceR) ⇐ Unit
  twiceIsEven 
    = begin

      twiceR ∙ evenR ⊆ evenR ∙ twiceR

    ⇐⟨ (tactic (by (quote evenLemma))) ⟩

      twiceR ∙ evenR ⊆ (ρ twiceR) ∙ twiceR

    ⇐⟨ (tactic (by (quote ρ-intro))) ⟩

      twiceR ∙ evenR ⊆ twiceR

    ⇐⟨ (tactic (by (quote ∙-id-r))) ⟩

      twiceR ∙ evenR ⊆ twiceR ∙ Id

    ⇐⟨ (λ x → ∙-mono (p1 x) (p2 x)) ⟩

      (twiceR ⊆ twiceR × evenR ⊆ Id)

    ⇐⟨ (λ _ → ⊆-refl , φ⊆Id (λ z → So (even z))) ⟩

      Unit

    ∎
