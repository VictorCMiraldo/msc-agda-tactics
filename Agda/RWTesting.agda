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

module RWTesting where


module Test where

    postulate
      blah : ∀{a}{A : Set a} → A

    fromJust! : ∀{a}{A : Set a} → Maybe A → A
    fromJust! (just x) = x
    fromJust! _        = blah

    ++-assoc : ∀{a}{A : Set a}(xs ys zs : List A) → 
               (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
    ++-assoc [] ys zs = refl
    ++-assoc (x ∷ xs) ys zs -- = cong (λ l → x ∷ l) (++-assoc xs ys zs)
               = tactic (by (quote ++-assoc))
  
    open ≡-Reasoning

    ++-assocH : ∀{a}{A : Set a}(xs ys zs : List A) →
                (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
    ++-assocH [] ys zs = 
              begin 
                ([] ++ ys) ++ zs
              ≡⟨ refl ⟩
                ys ++ zs
              ≡⟨ refl ⟩
                [] ++ (ys ++ zs)
              ∎
    ++-assocH {A = A} (x ∷ xs) ys zs =
              begin
                ((x ∷ xs) ++ ys) ++ zs
              ≡⟨ refl ⟩
                x ∷ (xs ++ ys) ++ zs
              ≡⟨ refl ⟩
                x ∷ ((xs ++ ys) ++ zs)
              ≡⟨ (tactic (by (quote ++-assocH))) ⟩ 
                x ∷ (xs ++ (ys ++ zs))
              ≡⟨ refl ⟩
                (x ∷ xs) ++ (ys ++ zs)
              ∎

    []-++-neutral : ∀{a}{A : Set a}(xs : List A)
                  → xs ++ [] ≡ xs
    []-++-neutral [] = refl
    []-++-neutral (x ∷ xs) = tactic (by (quote []-++-neutral))

    -- TODO: think about how would we modify Strategy.PropEq
    --       in such a way that it recognizes when it doesn't need a cong.
    test1 : (x y : ℕ) → (x + y) + 0 ≡ y + (x + 0)
    test1 x y
      = begin
        (x + y) + 0
      ≡⟨ (tactic (by (quote +-right-identity))) ⟩
        x + y
      ≡⟨ +-comm x y ⟩
        y + x
      ≡⟨ (tactic (by (quote +-right-identity))) ⟩
        (y + x) + 0
      ≡⟨ (tactic (by (quote +-assoc))) ⟩
        y + (x + 0)
      ∎

    -- This is pretty slow...
    test2 : (x y : ℕ) → (x + y) + 0 ≡ y + (x + 0)
    test2 x y
      = begin
        (x + y) + 0
      ≡⟨ (tactic (by*-≡ (quote +-comm ∷ quote +-assoc ∷ []))) ⟩
        y + (x + 0)
      ∎

module Test2 where

   open import Data.Unit using (Unit; unit)
   open import Data.Empty using (⊥; ⊥-elim)

   open import Rel.Core hiding (_∩_)
   -- open import Rel.Properties.Neutral
   open import Rel.Properties.Basic
   open import Rel.Core.Equality
   open import Rel.Reasoning.SubsetJudgement

   g1 : RTerm ⊥
   g1 = rapp (rdef (quote _⊆_)) (ivar 0 ∷ ivar 0 ∷ [])

   g2 : RTerm ⊥
   g2 = rapp (rdef (quote _⊆_))
     (ivar 0 ∷
      rapp (rdef (quote _∙_))
      (ivar 0 ∷ rapp (rdef (quote fun)) (rlam (ivar 0) ∷ []) ∷ [])
      ∷ [])
   
   goalTest1 : {A B : Set}(R : Rel A B) → (R ⊆ R ∙ Id) ⇐ Unit
   goalTest1 R 
     = begin
       R ⊆ R ∙ Id
     ⇐⟨ (tactic (by (quote ∙-id-r))) ⟩
       R ⊆ R
     ⇐⟨ (λ _ → ⊆-refl) ⟩
       Unit
     ∎

   -- It is interesting to see how, if we keep the parameters
   -- to ᵒ-∙-implicit, by doesn't find that it needs a ≡r-sym!
   -- why?
   goalTest2 : {A B C : Set}(S : Rel A B)(R : Rel B C)
             → (R ∙ S) ᵒ ≡r (S ᵒ ∙ Id) ∙ R ᵒ
   goalTest2 R S = tactic (by*-≡r (quote ᵒ-∙-distr ∷ quote ∙-id-r ∷ []))

   goalTest3 : {A B C : Set}(S : Rel A B)(R : Rel B C)
             → (R ∙ S) ᵒ ≡r (S ᵒ ∙ Id) ∙ R ᵒ
   goalTest3 S R = ≡r-trans
                     (≡r-cong (λ z → z) (≡r-sym (ᵒ-∙-distr S R)))
                     (≡r-cong (λ z → z ∙ R ᵒ) (∙-id-r (S ᵒ)))

     -- tactic (by*-≡r (quote ᵒ-∙-distr ∷ quote ∙-id-r ∷ []))

   last : ℕ
   last = {!!}
