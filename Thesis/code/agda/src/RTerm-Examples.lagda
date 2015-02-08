\begin{code}
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

open import RW.Language.RTerm
open import RW.Language.Unification hiding (_++_)
open import RW.Language.RTermUtils

open import Relation.Binary.PropositionalEquality
open import Data.List
open import Data.Unit using (Unit; unit)
open import Data.Empty using (⊥; ⊥-elim)

open import Rel.Core.Core hiding (_∩_)
open import Rel.Properties
open import Rel.Core.Equality
open import Rel.Reasoning.SubsetJudgement
open import Rel.Reasoning.RelationJudgement renaming (begin_ to rbegin_; _∎ to _r∎)
\end{code}

%<*imports>
\begin{code}
open import RW.Strategy.PropEq
open import Rel.Reasoning.RelEq-Strategy
open import RW.RW (≡-strat ∷ rel-strat ∷ [])
\end{code}
%</imports>


%<*example1>
\begin{code}
++-assoc : ∀{a}{A : Set a}(xs ys zs : List A)  
         → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc [] ys zs       = refl
++-assoc (x ∷ xs) ys zs = {! !}0
\end{code}
%</example1>


%<*example2>
\begin{code}
R⊆R∙Id : {A B : Set}(R : Rel A B) 
         → (R ⊆ R ∙ Id) ⇐ Unit
R⊆R∙Id R 
  = begin
    R ⊆ R ∙ Id
  ⇐⟨ {! !}1 ⟩
    R ⊆ R
  ⇐⟨ (λ _ → ⊆-refl) ⟩
    Unit
  ∎
\end{code}
%</example2>
