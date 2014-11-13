module Rel.CaseStudies.Simple1 where

open import Data.Bool using (Bool; true; false)
open import Relation.Binary.PropositionalEquality
open import Data.Product using (_×_; ∃; _,_) renaming (proj₁ to p1; proj₂ to p2)
open import Data.Sum using (_⊎_; [_,_]) renaming (inj₁ to i1; inj₂ to i2; [_,_]′ to case)
open import Function using (id; _∘_)

open import Data.Unit using (Unit; unit)
open import Data.Empty using (⊥; ⊥-elim)

open import Data.Nat using (ℕ; zero; suc; _+_; _*_)

open import Rel.Core.Core
open import Rel.Core.Correflexive
open import Rel.Core.Equality
open import Rel.Reasoning.SubsetJudgement
open import Rel.Reasoning.RelationJudgement renaming (begin_ to rbegin_; _∎ to _r∎)
open import Rel.Properties

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

lemma-+zero : ∀ a
            → a + zero ≡ a
lemma-+zero zero = refl
lemma-+zero (suc a) = cong suc (lemma-+zero a)

lemma-+succ : ∀ a b 
            → suc a + b ≡ a + suc b
lemma-+succ zero b = refl
lemma-+succ (suc a) b = cong suc (lemma-+succ a b)

twiceIsN+N : (n : ℕ) → twice n ≡ n + n
twiceIsN+N zero = refl
twiceIsN+N (suc n) = cong suc (trans (cong suc (twiceIsN+N n)) (lemma-+succ n n))

twiceIsTwice : (n : ℕ) → twice n ≡ 2 * n
twiceIsTwice zero = refl
twiceIsTwice (suc n) rewrite lemma-+zero n
  = cong suc (trans (cong suc (twiceIsN+N n)) (lemma-+succ n n)) 

n*2-IsEven : (n : ℕ) → even (2 * n) ≡ true
n*2-IsEven zero    = refl
n*2-IsEven (suc n) 
  rewrite lemma-+zero n
  | sym (lemma-+succ n n)
    = subst (λ x → even (n + x) ≡ true) (lemma-+zero n) (n*2-IsEven n)

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
evenLemma1 b b' bTb 
  = let a = p1 (p1 bTb)
    in sym (p2 bTb) , evenLemma1Aux a b (p1 (p2 (p1 bTb)))
  where 
    evenLemma1Aux : (a : ℕ) → (b : ℕ) → twice a ≡ b → So (even b)
    evenLemma1Aux a b a*2≡b 
      rewrite sym a*2≡b
      | twiceEven a = unit

evenLemma2 : evenR ⊆ ρ twiceR
evenLemma2 b b' bEvena 
  = let evenb = p2 bEvena
        a , btwicea = evenLemma2Aux b evenb
    in (a , btwicea , subst (λ x → twice a ≡ x) (p1 bEvena) btwicea) 
      , sym (p1 bEvena)
  where
    evenLemma2Aux : (b : ℕ) → So (even b) 
                  → ∃ (λ x → twiceR b x)
    evenLemma2Aux b so with div2 b so | div2-twice-cancel b so
    evenLemma2Aux b so | a | prf with even b
    evenLemma2Aux b () | _ | prf | false 
    evenLemma2Aux b _  | a | prf | true = a , prf
     
-- Finally, our lemma.
evenLemma : ρ twiceR ≡r evenR
evenLemma = evenLemma1 , evenLemma2

-- * End of assumption
--------------------------------------------------------------
-- * Promotion rule. This is the problem we're stuck at,
--   at the moment.
--

≡r-promote : {A B : Set}{R S : Rel A B}
           → R ≡r S → R ≡ S
≡r-promote (r⊆s , s⊆r) = {!!}

-------------------------------------------------------------
-- * The actual equational proof that twice respects even.

twiceIsEven : (twiceR ∙ evenR ⊆ evenR ∙ twiceR) ⇐ Unit
twiceIsEven 
  = begin

    twiceR ∙ evenR ⊆ evenR ∙ twiceR

  ⇐⟨ subst (λ x → twiceR ∙ evenR ⊆ x ∙ twiceR) (≡r-promote evenLemma) ⟩

    twiceR ∙ evenR ⊆ ρ twiceR ∙ twiceR

  ⇐⟨ subst (λ x → twiceR ∙ evenR ⊆ x) (≡r-promote (ρ-intro twiceR)) ⟩

    twiceR ∙ evenR ⊆ twiceR

  ⇐⟨ subst (λ x → twiceR ∙ evenR ⊆ x) (≡r-promote (≡r-sym (∙-id-r twiceR))) ⟩

    twiceR ∙ evenR ⊆ twiceR ∙ Id

  ⇐⟨ ∙-monotony ⟩

    (twiceR ⊆ twiceR × evenR ⊆ Id)

  ⇐⟨ (λ _ → ⊆-refl , φ⊆Id) ⟩

    Unit

  ∎