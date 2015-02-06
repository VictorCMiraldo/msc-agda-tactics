module Rel.CaseStudies.Simple1 where

open import Data.Bool using (Bool; true; false)
open import Relation.Binary.PropositionalEquality
open import Data.Product using (_×_; ∃; _,_) renaming (proj₁ to p1; proj₂ to p2)
open import Data.Sum using (_⊎_; [_,_]) renaming (inj₁ to i1; inj₂ to i2; [_,_]′ to case)
open import Function using (id; _∘_; _$_)

open import Data.Unit using (Unit; unit)
open import Data.Empty using (⊥; ⊥-elim)

open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Nat.Properties.Simple
  using (+-suc; +-right-identity)

open import Data.List using (List; []; _∷_)

open import Rel.Core.Core hiding (_∩_)
open import Rel.Core.Correflexive
open import Rel.Core.Equality
open import Rel.Reasoning.SubsetJudgement
open import Rel.Reasoning.RelationJudgement renaming (begin_ to rbegin_; _∎ to _r∎)
open import Rel.Properties

open import RW.Language.RTerm
open import RW.Language.RTermUtils

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
    in cons-ρ $ 
         (a , btwicea , cons-fun 
            (subst (λ x → twice a ≡ x) (p1 $ φ.un bEvena) (fun.un btwicea))) 
       , (p1 $ φ.un bEvena)
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

-- * End of assumption
-------------------------------------------------------------
-------------------------------------------------------------
-- * The actual equational proof that twice respects even.

open import RW.Language.RTerm
open import RW.Language.RTermUtils
open import RW.Language.Unification
open import RW.Strategy

open import Rel.Reasoning.RelEq-Strategy using (rel-strat)
open import RW.RW (rel-strat ∷ [])

test : (twiceR ∙ evenR ⊆ evenR ∙ twiceR) ⇐ (twiceR ∙ evenR ⊆ ρ twiceR ∙ twiceR)
test = {!!}

goal₂ : RBinApp ℕ
goal₂ = (impl ,
 rapp (rdef (quote _⊆_))
 (rapp (rdef (quote _∙_))
  (rapp (rdef (quote fun)) (rapp (rdef (quote twice)) [] ∷ []) ∷
   rapp (rdef (quote φ))
   (rlam
    (rapp (rdef (quote So))
     (rapp (rdef (quote even)) (ivar 0 ∷ []) ∷ []))
    ∷ [])
   ∷ [])
  ∷
  rapp (rdef (quote _∙_))
  (rapp (rdef (quote fun)) (rapp (rdef (quote twice)) [] ∷ []) ∷
   rapp (rdef (quote fun)) (rlam (ivar 0) ∷ []) ∷ [])
  ∷ [])
 ,
 rapp (rdef (quote _⊆_))
 (rapp (rdef (quote _∙_))
  (rapp (rdef (quote fun)) (rapp (rdef (quote twice)) [] ∷ []) ∷
   rapp (rdef (quote φ))
   (rlam
    (rapp (rdef (quote So))
     (rapp (rdef (quote even)) (ivar 0 ∷ []) ∷ []))
    ∷ [])
   ∷ [])
  ∷
  rapp (rdef (quote fun)) (rapp (rdef (quote twice)) [] ∷ []) ∷ []))

ty₂ : RBinApp ℕ
ty₂ = (rdef (quote _≡r_) ,
 ivar 0 ,
 rapp (rdef (quote _∙_))
 (ivar 0 ∷ rapp (rdef (quote fun)) (rlam (ivar 0) ∷ []) ∷ []))

ty₂! : RBinApp ℕ
ty₂! = (rdef (quote _≡r_) ,
 ovar 0 ,
 rapp (rdef (quote _∙_))
 (ovar 0 ∷ rapp (rdef (quote fun)) (rlam (ivar 0) ∷ []) ∷ []))

ξ₁ : ∀{a}{A : Set a} → RBinApp A → RTermName
ξ₁ (x , _ , _) = x

ξ₂ : ∀{a}{A : Set a} → RBinApp A → RTerm A
ξ₂ (_ , x , _) = x

ξ₃ : ∀{a}{A : Set a} → RBinApp A → RTerm A
ξ₃ (_ , _ , x) = x

open import Data.Maybe using (Maybe; nothing; just)
postulate
  come-on : ∀{a}{A : Set a} → A

fromJust! : ∀{a}{A : Set a} → Maybe A → A
fromJust! (just a) = a
fromJust! _        = come-on

twiceIsEven : (twiceR ∙ evenR ⊆ evenR ∙ twiceR) ⇐ Unit
twiceIsEven 
  = begin

    twiceR ∙ evenR ⊆ evenR ∙ twiceR

  -- ⇐⟨ ≡r-subst (λ x → twiceR ∙ evenR ⊆ x ∙ twiceR) evenLemma ⟩
  ⇐⟨ (tactic (by (quote evenLemma))
     ) ⟩

    twiceR ∙ evenR ⊆ (ρ twiceR) ∙ twiceR

  -- ⇐⟨ ≡r-subst (λ x → twiceR ∙ evenR ⊆ x) (ρ-intro twiceR) ⟩
  ⇐⟨ (tactic (by-static (quote ρ-intro))) ⟩
  {-
  
    -}

    twiceR ∙ evenR ⊆ twiceR

  -- ⇐⟨ ≡r-subst (λ x → twiceR ∙ evenR ⊆ x) (≡r-sym (∙-id-r twiceR)) ⟩
  ⇐⟨ (let g1 = ξ₂ goal₂
          g2 = ξ₃ goal₂
          t1 = ξ₂ ty₂!
          t2 = ξ₃ ty₂!
          g□  = g1 ∩ g2
          g□↑ = g1 ∩↑ g2
          u11 = fromJust! $ g□↑ -↓ g1
          u12 = fromJust! $ g□↑ -↓ g2
          -- THE PROBLEM:
          --   plug a chain of transformations to our 
          --   strategy pipeline.
        in {!!}
     ) ⟩
  -- ⇐⟨ (tactic (by-static (quote ∙-id-r))) ⟩

    twiceR ∙ evenR ⊆ twiceR ∙ Id

  ⇐⟨ ∙-monotony ⟩

    (twiceR ⊆ twiceR × evenR ⊆ Id)

  ⇐⟨ (λ _ → ⊆-refl , φ⊆Id) ⟩

    Unit

  ∎


