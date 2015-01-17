open import Level using (Level)
open import Function using (_∘_; id; flip)
open import Data.Fin as Fin using (Fin; fromℕ; fromℕ≤) renaming (zero to fz; suc to fs)
open import Data.Nat as Nat using (ℕ; suc; zero; _+_; _⊔_; decTotalOrder; _<_; _≤_; s≤s; z≤n; _∸_) renaming (_≟_ to _≟-ℕ_)
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
open import Data.Empty using (⊥; ⊥-elim)

open import RWUtils

module Term2RTerm where

  open DecTotalOrder Nat.decTotalOrder using (total)

  -- An error postulate for unsuported syntax;
  postulate
    unsuportedSyntax : ∀{a}{A : Set a} → String → A

  -- In the same fashion as "Auto in Agda", we'll define
  -- implication (or, "→") as a Name, so we can easily
  -- handle it in RTerm's.
  data TermName : Set₀ where
    name : (n : Name) → TermName
    impl : TermName

  name-inj : ∀ {x y} → TermName.name x ≡ TermName.name y → x ≡ y
  name-inj refl = refl

  _≟-TermName_ : (x y : TermName) → Dec (x ≡ y)
  _≟-TermName_ (name x) (name  y) with x ≟-Name y
  _≟-TermName_ (name x) (name .x) | yes refl = yes refl
  _≟-TermName_ (name x) (name  y) | no  x≠y  = no (x≠y ∘ name-inj)
  _≟-TermName_ (name _)  impl     = no (λ ())
  _≟-TermName_  impl    (name _)  = no (λ ())
  _≟-TermName_  impl     impl     = yes refl

  open import RTerm TermName _≟-TermName_ Literal _≟-Lit_
    as RTerm public
  open DistributiveLattice ℕ-Props.distributiveLattice using (_∧_; ∧-comm)

  open Inject {{...}}
  open Raise {{...}}

  private
    supremumLemma : ∀{m n} → m ≤ n → m ∧ n ≡ n
    supremumLemma z≤n     = refl
    supremumLemma (s≤s p) = cong suc (supremumLemma p)

  -- Match indexes of injectable types.
  match : ∀{m n} {I J} ⦃ i : Inject I ⦄ ⦃ j : Inject J ⦄
        → I m → J n → I (m ∧ n) × J (m ∧ n)
  match {m} {n} i j with total m n
  ...| inj₁ m≤n rewrite supremumLemma m≤n = inject≤ m≤n i , j
  ...| inj₂ n≤m rewrite ∧-comm m n
                      | supremumLemma n≤m = i , inject≤ n≤m j

  private
    injectInternal≤ : ∀{o i₁ i₂} → i₁ ≤ i₂ → RTerm i₁ o → RTerm i₂ o
    injectInternal≤ {o} {i₁} {i₂} prf rt
      = fixTerm {o} {i₁} {i₂} prf (Δ-correct prf) (injectInternal (Δ prf) rt)
      where
        fixTerm : ∀{o i₁ i₂} (prf : i₁ ≤ i₂) 
                → i₂ ≡ i₁ + Δ prf
                → RTerm (i₁ + Δ prf) o
                → RTerm i₂ o
        fixTerm z≤n rt = id
        fixTerm (s≤s prf) rt rewrite sym rt
          = id
    

    matchInternal : ∀{i₁ i₂ o} → RTerm i₁ o → RTerm i₂ o 
                  → RTerm (i₁ ∧ i₂) o × RTerm (i₁ ∧ i₂) o
    matchInternal {i₁} {i₂} t1 t2 with total i₁ i₂
    ...| inj₂ i1>i2 rewrite ∧-comm i₁ i₂
                          | supremumLemma i1>i2
                    = t1 , injectInternal≤ i1>i2 t2
    ...| inj₁ i1≤i2 rewrite supremumLemma i1≤i2
                    = injectInternal≤ i1≤i2 t1 , t2
  
    matchInternalL : ∀{i₁ i₂ o} → RTerm i₁ o → List (RTerm i₂ o)
                   → RTerm (i₁ ∧ i₂) o × List (RTerm (i₁ ∧ i₂) o)
    matchInternalL {i1} {i2} t []  with total i1 i2
    ...| inj₁ i1≤i2 rewrite supremumLemma i1≤i2
                          = injectInternal≤ i1≤i2 t , []
    ...| inj₂ i1>i2 rewrite ∧-comm i1 i2
                        | supremumLemma i1>i2 
                        = t , []
    matchInternalL t (ht ∷ ts) 
      = proj₁ (matchInternal t ht)
      , map (proj₂ ∘ matchInternal t) (ht ∷ ts)

  ∃RTerm : Set
  ∃RTerm = ∃ (λ { (i , o) → RTerm i o })

  ∃RTerm₂ : Set
  ∃RTerm₂ = ∃ (λ { (i , o) → RTerm i o × RTerm i o })

  ∃RTerms : Set
  ∃RTerms = ∃ (λ { (i , o) → List (RTerm i o) })

  convertℕ : ℕ → RTerm 0 0
  convertℕ zero    = rcon (name (quote zero)) []
  convertℕ (suc n) = rcon (name (quote suc)) (convertℕ n ∷ [])

  m≤n∧m≠n→m<n : ∀{m n} → (m ≡ n → ⊥) → m ≤ n → suc m ≤ n
  m≤n∧m≠n→m<n {.zero} {zero} m≠n z≤n = ⊥-elim (m≠n refl) 
  m≤n∧m≠n→m<n {.zero} {suc n} m≠n z≤n = s≤s z≤n
  m≤n∧m≠n→m<n m≠n (s≤s m≤n) = s≤s (m≤n∧m≠n→m<n (m≠n ∘ cong suc) m≤n)

  mutual
    {- TODO:
         Figure out what's happening in (convert d (var _ _)).
         ivar's are never starting at 0... why?

       TODO:
         lambda's should use injectInternal, instead of raise internal.
    -}
    convert : ℕ → AgTerm → ∃RTerm
    convert d (var x []) with total d x
    ...| inj₁ d≤x = (suc (Δ d≤x) , 0) , ivar (fromℕ (Δ d≤x))
    ...| inj₂ d>x = (0 , suc (d ∸ Δ d>x)) , ovar (fromℕ (d ∸ Δ d>x))
    convert d (lit (nat n)) = (0 , 0) , convertℕ n
    convert d (lit l)      = (0 , 0) , rlit l
    convert d (con c args) with convertChildren d args
    ...| ios , args' = ios , rcon (name c) args'
    convert d (def f args) with convertChildren d args
    ...| ios , args' = ios , rcon (name f) args'
    convert d (pi (arg (arg-info visible _) (el _ t₁)) (abs _ (el _ t₂)))
      with convert d t₁ | convert (suc d) t₂
    ...| (i1 , o1) , t1 | (i2 , o2) , t2 =
      let ot1  , ot2  = match t1 t2
          iot1 , iot2 = matchInternal ot1 ot2
      in (i1 ∧ i2 , o1 ∧ o2) , rcon impl (iot1 ∷ iot2 ∷ [])
    convert d (pi _ (abs _ (el _ t₂))) = convert (suc d) t₂
    convert d (lam _ (abs _ l)) with convert (suc d) l
    ...| (i , o) , l'  = (i , o) , rlam (i+1≡suci (injectInternal 1 l'))
      where
        i+1≡suci : ∀{i o} → RTerm (i + 1) o → RTerm (suc i) o
        i+1≡suci {i} rt rewrite +-comm i 1 = rt
    convert d (pat-lam cs args) 
      = unsuportedSyntax "pattern matching lambdas" 
    convert d (var x xs) 
      = unsuportedSyntax "var with args"
    convert d (sort s)
      = unsuportedSyntax "sort"
    convert d unknown 
      = unsuportedSyntax "unknown"

    convertChildren : ℕ → List (Arg AgTerm) → ∃RTerms
    convertChildren d []       = (0 , 0) , []
    convertChildren d (arg (arg-info visible _) x ∷ xs) 
      with convert d x | convertChildren d xs 
    ...| (ix , ox) , x' | (ixs , oxs) , xs' with match x' xs'
    ...| (mx , mxs) with matchInternalL mx mxs
    ...| (r , rs) = (ix ∧ ixs , ox ∧ oxs) , r ∷ rs
    convertChildren d (_ ∷ xs) = convertChildren d xs

  convert₂ : ℕ → AgTerm → AgTerm → ∃RTerm₂
  convert₂ d t1 t2 with convert d t1 | convert d t2
  ...| (i1 , o1) , t1' | (i2 , o2) , t2' with match t1' t2'
  ...| mt1 , mt2 with matchInternal mt1 mt2
  ...| r1 , r2 = (i1 ∧ i2 , o1 ∧ o2) , r1 , r2

    
  showAgTerm : ℕ → AgTerm → String
  showAgTerm d = (showRTerm showTermName showLiteral) ∘ proj₂ ∘ convert d
    where
      ignoreQualification : String → String
      ignoreQualification s = Str.fromList (iqAux (Str.toList s) [])
        where
          iqAux : List Char → List Char → List Char
          iqAux []         acu = acu
          iqAux ('.' ∷ cs) acu = iqAux cs []
          iqAux (c   ∷ cs) acu = iqAux cs (acu ++ (c ∷ []))

      showTermName : TermName → String
      showTermName (name n) = ignoreQualification (showName n)
      showTermName impl     = "→"
