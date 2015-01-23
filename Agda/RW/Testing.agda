open import Level using (Level)
open import Function using (_∘_; id; flip)
open import Data.Fin as Fin using (Fin; fromℕ) renaming (zero to fz; suc to fs)
open import Data.Nat as Nat using (ℕ; suc; zero; _+_; _⊔_; decTotalOrder; _<_; _≤_; s≤s; z≤n) renaming (_≟_ to _≟-ℕ_)
open import Data.Nat.Properties.Simple using (+-comm)
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

open import RTerm

module Testing where


module Test where

    open import RTermUtils
    open import Relation.Binary.PropositionalEquality
    open import Data.List

    t1 : RTerm ℕ
    t1 = rapp (rcon (quote List._∷_))
              ( ivar 3 
              ∷ rapp (rdef (quote _++_))
                     ( rapp (rdef (quote _++_))
                            ( ivar 2 
                            ∷ ivar 1
                            ∷ [])
                     ∷ ivar 0
                     ∷ [])
              ∷ [])

    t2 : RTerm ℕ
    t2 = rapp (rcon (quote List._∷_))
              ( ivar 3
              ∷ rapp (rdef (quote _++_))
                     ( ivar 2
                     ∷ rapp (rdef (quote _++_))
                            ( ivar 1
                            ∷ ivar 0
                            ∷ [])
                     ∷ [])
              ∷ [])
    
    tG : RTerm ℕ
    tG = rapp (rdef (quote _≡_)) (t1 ∷ t2 ∷ [])

    tA : RTerm ℕ
    tA = rapp (rdef (quote _≡_))
              ( rapp (rdef (quote _++_))
                     ( rapp (rdef (quote _++_))
                            ( ivar 2
                            ∷ ivar 1
                            ∷ [])
                     ∷ ivar 0
                     ∷ [])
              ∷ rapp (rdef (quote _++_))
                     ( ivar 2
                     ∷ rapp (rdef (quote _++_))
                            ( ivar 1
                            ∷ ivar 0
                            ∷ [])
                     ∷ [])
              ∷ [])

    postulate
      blah : ∀{a}{A : Set a} → A

    fromJust! : ∀{a}{A : Set a} → Maybe A → A
    fromJust! (just a) = a
    fromJust! nothing  = blah

    fromTl! : ∀{a}{A : Set a} → List A → A × A
    fromTl! (a ∷ b ∷ []) = a , b
    fromTl! _            = blah
    
    {-
    res : RTerm 4 0
    res = let (n , a , b) = fromJust! (stripEqHead tG tA)
              (a1 , a2)   = fromTl! a
              (b1 , b2)   = fromTl! b
          in {!a2 - b2!}
    -}

    mycong : ∀{a}{A B : Set a}(f : A → B)
           → {x y : A} → x ≡ y → f x ≡ f y
    mycong f {x} {y} x≡y = subst (λ a → f x ≡ f a) x≡y refl

    mutual
      ++-assoc-quote : AgTerm
      ++-assoc-quote = def (quote ++-assoc)
                     (arg (arg-info hidden relevant) (var 5 []) ∷
                      arg (arg-info hidden relevant) (var 4 []) ∷
                      arg (arg-info visible relevant) (var 2 []) ∷
                      arg (arg-info visible relevant) (var 1 []) ∷
                      arg (arg-info visible relevant) (var 0 []) ∷ [])

      ++-assoc : ∀{a}{A : Set a}(xs ys zs : List A) → 
                 (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
      ++-assoc [] ys zs = refl
      ++-assoc (x ∷ xs) ys zs -- = cong (λ l → x ∷ l) (++-assoc xs ys zs)
               = quoteGoal g in {!(t1 ∩↑ t2) - t2!}
 
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
           -- ≡⟨ mycong (_∷_ x) (++-assocH xs ys zs) ⟩
              ≡⟨ {!!} ⟩ --  quoteGoal g in unquote (RW (quoteTerm ++-assocH xs ys zs) g) ⟩ 
           -- ≡⟨ cong (_∷_ x) (++-assocH xs ys zs) ⟩
                x ∷ (xs ++ (ys ++ zs))
              ≡⟨ refl ⟩
                (x ∷ xs) ++ (ys ++ zs)
              ∎

    []-++-neutral : ∀{a}{A : Set a}(xs : List A)
                  → xs ++ [] ≡ xs
    []-++-neutral xs = {!!}

module Test2 where
  
   open import RTermUtils
   open import Relation.Binary.PropositionalEquality
   open import Data.List

   open import Data.Unit using (Unit; unit)
   open import Data.Empty using (⊥; ⊥-elim)

   open import Rel.Core.Core hiding (_∩_)
   open import Rel.Properties
   open import Rel.Core.Equality
   open import Rel.Reasoning.SubsetJudgement
   open import Rel.Reasoning.RelationJudgement renaming (begin_ to rbegin_; _∎ to _r∎)

   f : Name → RTermName
   f = rdef

   t1 : RTerm ℕ
   t1 = rapp (f (quote _⊆_))
             (ivar 0 ∷ ivar 0 ∷ [])

   t2 : RTerm ℕ
   t2 = rapp (f (quote _⊆_))
             ( ivar 0 
             ∷ rapp (f (quote _∙_))
               ( ivar 0 
               ∷ rapp (f (quote fun))
                      ((rlam (ivar 0))
                      ∷ [])
               ∷ [])
             ∷ [])

   tG : RTerm ℕ
   tG = rapp impl (t1 ∷ t2 ∷ [])

   tA : RTerm ℕ
   tA = rapp (f (quote _≡r_))
             ( ivar 0
             ∷ rapp (f (quote _∙_))
                    ( ivar 0
                    ∷ rapp (f (quote fun))
                           (rlam (ivar 0)
                           ∷ [])
                    ∷ [])
             ∷ [])

   unel : Type → AgTerm
   unel (el _ t) = t
   
   goalTest1 : {A B : Set}(R : Rel A B) → (R ⊆ R ∙ Id) ⇐ Unit
   goalTest1 R 
     = begin
       R ⊆ R ∙ Id
     ⇐⟨(quoteGoal g in {! Ag2RTerm (quoteTerm (λ x → δ x ∙ R))!}) ⟩
       R ⊆ R
     ⇐⟨ (λ _ → ⊆-refl) ⟩
       Unit
     ∎
