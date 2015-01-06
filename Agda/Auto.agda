open import Level using (Level)
open import Function using (_∘_; id; flip)
open import Data.Fin as Fin using (Fin; fromℕ)
open import Data.Nat as Nat using (ℕ; suc; zero; _+_; _⊔_; decTotalOrder; _<_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties.Simple using (+-comm)
open import Data.Nat.Properties as ℕ-Props
open import Data.Nat.Show using (show)
open import Data.String as Str renaming (_++_ to _++s_)
open import Data.List as List using (List; []; _∷_; [_]; concatMap; _++_; length; map)
open import Data.Vec as Vec using (Vec; []; _∷_; _∷ʳ_; reverse; initLast; toList)
open import Data.Product as Prod using (∃; _×_; _,_; proj₁; proj₂)
open import Data.Maybe as Maybe using (Maybe; just; nothing; maybe)
open import Data.Sum as Sum using (_⊎_; inj₁; inj₂)
open import Data.Integer as Int using (ℤ; -[1+_]; +_) renaming (_≟_ to _≟-Int_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary using (module DecTotalOrder)
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_; refl; cong; sym)
open import Reflection renaming (Term to AgTerm; _≟_ to _≟-AgTerm_)
open import Algebra using (module CommutativeSemiring; module DistributiveLattice)

module Auto where

  open DecTotalOrder Nat.decTotalOrder using (total)

  private
    ∃-syntax : ∀ {a b} {A : Set a} → (A → Set b) → Set (b Level.⊔ a)
    ∃-syntax = ∃
    syntax ∃-syntax (λ x → B) = ∃[ x ] B


  -- define error messages that may occur when the `auto` function is
  -- called.
  data Message : Set where
    searchSpaceExhausted : Message
    unsupportedSyntax    : String → Message


  -- define our own instance of the error functor based on the either
  -- monad, and use it to propagate one of several error messages
  private
    Error : ∀ {a} (A : Set a) → Set a
    Error A = Message ⊎ A

    _⟨$⟩_ : ∀ {a b} {A : Set a} {B : Set b} (f : A → B) → Error A → Error B
    f ⟨$⟩ inj₁ x = inj₁ x
    f ⟨$⟩ inj₂ y = inj₂ (f y)


  -- define term names for the term language we'll be using for proof
  -- search; we use standard Agda names, together with term-variables
  -- and Agda implications/function types.
  data TermName : Set₀ where
    name : (n : Name) → TermName
    tvar : (i : ℤ)    → TermName
    impl : TermName

  name-inj : ∀ {x y} → TermName.name x ≡ TermName.name y → x ≡ y
  name-inj refl = refl

  tvar-inj : ∀ {i j} → tvar i ≡ tvar j → i ≡ j
  tvar-inj refl = refl

  _≟-TermName_ : (x y : TermName) → Dec (x ≡ y)
  _≟-TermName_ (name x) (name  y) with x ≟-Name y
  _≟-TermName_ (name x) (name .x) | yes refl = yes refl
  _≟-TermName_ (name x) (name  y) | no  x≠y  = no (x≠y ∘ name-inj)
  _≟-TermName_ (name _) (tvar _)  = no (λ ())
  _≟-TermName_ (name _)  impl     = no (λ ())
  _≟-TermName_ (tvar _) (name _)  = no (λ ())
  _≟-TermName_ (tvar i) (tvar  j) with i ≟-Int j
  _≟-TermName_ (tvar i) (tvar .i) | yes refl = yes refl
  _≟-TermName_ (tvar i) (tvar  j) | no i≠j = no (i≠j ∘ tvar-inj)
  _≟-TermName_ (tvar _)  impl     = no (λ ())
  _≟-TermName_  impl    (name _)  = no (λ ())
  _≟-TermName_  impl    (tvar _)  = no (λ ())
  _≟-TermName_  impl     impl     = yes refl


  -- define rule names for the proof terms/rules that our proof search will
  -- return/use; we'll use standard Agda names, together with rule-variables.
  data RuleName : Set where
    name : Name → RuleName
    rvar : ℕ    → RuleName


  -- now we can load the definitions from proof search
  -- open import ProofSearch RuleName TermName _≟-TermName_ Literal _≟-Lit_
       -- as PS public renaming (Term to PsTerm)
  open import Unification TermName _≟-TermName_ Literal _≟-Lit_
    as U public renaming (Term to PsTerm)
  open DistributiveLattice ℕ-Props.distributiveLattice using (_∧_; ∧-comm)

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

  -- type class for injections in the fashion of Fin.inject+
  record Inject (T : ℕ → Set) : Set where
    field
      inject : ∀ {m} n → T m → T (m + n)

    inject≤ : ∀ {m n} → m ≤ n → T m → T n
    inject≤ {m} {n} p t = PropEq.subst T (sym (Δ-correct p)) (inject (Δ p) t)

  open Inject {{...}} using (inject; inject≤)


  -- type class for raising in the fashion of Fin.raise
  record Raise (T : ℕ → Set) : Set where
    field
      raise : ∀ {m} n → T m → T (n + m)

    raise≤ : ∀ {m n} → m ≤ n → T m → T n
    raise≤ {m} {n} p t = PropEq.subst T (sym (PropEq.trans (Δ-correct p) (+-comm m (Δ p)))) (raise (Δ p) t)

  open Raise {{...}} using (raise; raise≤)


  -- instances for inject/raise for all used data types
  instance
    InjectFin   : Inject Fin
    InjectFin   = record { inject = Fin.inject+ }
    RaiseFin    : Raise  Fin
    RaiseFin    = record { raise  = Fin.raise }
    InjectTerm  : Inject PsTerm
    InjectTerm  = record { inject = λ n → replace (var ∘ inject n) }
    RaiseTerm   : Raise  PsTerm
    RaiseTerm   = record { raise  = λ m → replace (var ∘ raise m) }
    InjectTerms : Inject (List ∘ PsTerm)
    InjectTerms = record { inject = λ n → List.map (inject n) }
    RaiseTerms  : Raise  (List ∘ PsTerm)
    RaiseTerms  = record { raise  = λ m → List.map (raise m) }
    InjectGoals : ∀ {k} → Inject (λ n → Vec (PsTerm n) k)
    InjectGoals = record { inject = λ n → Vec.map (inject n) }
    RaiseGoals  : ∀ {k} → Raise (λ n → Vec (PsTerm n) k)
    RaiseGoals  = record { raise  = λ m → Vec.map (raise m) }
    -- InjectRule  : Inject Rule
    -- InjectRule  = record { inject = λ n → λ { (rule nm c p) → rule nm (inject n c) (inject n p) } }
    -- RaiseRule   : Raise Rule
    -- RaiseRule   = record { raise  = λ m → λ { (rule nm c p) → rule nm (raise m c) (raise m p) } }

  -- could rephrase inject/raise in terms of allowing modification by
  -- a function ℕ → ℕ, but really... why would I... it makes all the
  -- other instances much, much more obtuse
  injectSubst : ∀ {m n} (δ : ℕ) → Subst m n → Subst (m + δ) (n + δ)
  injectSubst _ nil = nil
  injectSubst δ (snoc s t x) = snoc (injectSubst δ s) (inject δ t) (inject δ x)


  private
    m≤n→m⊔n=n : ∀ {m n} → m ≤ n → m ∧ n ≡ n
    m≤n→m⊔n=n  z≤n    = refl
    m≤n→m⊔n=n (s≤s p) = cong suc (m≤n→m⊔n=n p)


  -- match indices of injectable data types
  match : ∀ {m n} {I J} {{i : Inject I}} {{j : Inject J}}
        → I m → J n → I (m ∧ n) × J (m ∧ n)
  match {m} {n} i j with total m n
  ... | inj₁ p rewrite              m≤n→m⊔n=n p = (inject≤ p i , j)
  ... | inj₂ p rewrite ∧-comm m n | m≤n→m⊔n=n p = (i , inject≤ p j)


  -- next up, converting the terms returned by Agda's reflection
  -- mechanism to terms in our proof search's language!


  -- dictionary for the treatment of variables in conversion from Agda
  -- terms to terms to be used in proof search.
  ConvertVar : Set
  ConvertVar = (depth index : ℕ) → ∃ PsTerm

  -- conversion dictionary for rule-terms, which turns every variable
  -- that is within the scope of the term (i.e. is defined within the
  -- term by lambda abstraction) into a variable, and every variable
  -- which is defined out of scope into a Skolem constant (which
  -- blocks unification).
  convertVar4Term : ConvertVar
  convertVar4Term = fromVar
    where
      fromVar : (depth index : ℕ) → ∃ PsTerm
      fromVar d i with total i d
      fromVar d i | inj₁ i≤d = (suc (Δ i≤d) , var (fromℕ (Δ i≤d)))
      fromVar d i | inj₂ i>d = (0 , con (tvar (-[1+ Δ i>d ])) [])

  -- conversion dictionary for goal-terms, which turns all variables
  -- into Skolem constants which blocks all unification.
  convertVar4Goal : ConvertVar
  convertVar4Goal = fromVar
    where
      fromVar : (depth index : ℕ) → ∃ PsTerm
      fromVar d i with total i d
      fromVar d i | inj₁ i≤d = (0 , con (tvar (+ Δ i≤d)) [])
      fromVar d i | inj₂ i>d = (0 , con (tvar (-[1+ Δ i>d ])) [])


  -- helper function for converting definitions or constructors to
  -- proof terms.
  fromDefOrCon : (s : Name) → ∃[ n ] List (PsTerm n) → ∃ PsTerm
  fromDefOrCon f (n , ts) = n , con (name f) ts


  -- specialised function to convert literals of natural numbers
  -- (since they have a representation using Agda names)
  convertℕ : ℕ → PsTerm 0
  convertℕ  zero   = con (name (quote zero)) []
  convertℕ (suc n) = con (name (quote suc)) (convertℕ n ∷ [])


  -- convert an Agda term to a term, abstracting over the treatment of
  -- variables with an explicit dictionary of the type `ConvertVar`---
  -- passing in `ConvertVar4Term` or `ConvertVar4Goal` will result in
  -- rule-terms or goal-terms, respectively.
  mutual
    convert : ConvertVar → (depth vars : ℕ) → AgTerm → Error (∃ PsTerm)
    convert cv d v (lit (nat n)) = inj₂ (0 , convertℕ n)
    convert cv d v (lit l)       = inj₂ (0 , lit l)
    convert cv d v (var i [])    = inj₂ (cv d i)
    {-
      with total v i
    -- v ≤ i branch
    ...| inj₁ x = inj₂ (cv d (i -Δ- x)) -- inj₂ (cv d i)
    -- i < v branch
    ...| inj₂ y = inj₂ (0 , lvar i)
    -}
    convert cv d v (var i args)  = inj₁ (unsupportedSyntax "var with args")
    convert cv d v (con c args)  = fromDefOrCon c ⟨$⟩ convertChildren cv d v args
    convert cv d v (def f args)  = fromDefOrCon f ⟨$⟩ convertChildren cv d v args
    convert cv d v (pi (arg (arg-info visible _) (el _ t₁)) (abs _ (el _ t₂)))
      with convert cv d v t₁ | convert cv (suc d) v t₂
    ... | inj₁ msg | _        = inj₁ msg
    ... | _        | inj₁ msg = inj₁ msg
    ... | inj₂ (n₁ , p₁) | inj₂ (n₂ , p₂)
      with match p₁ p₂
    ... | (p₁′ , p₂′) = inj₂ (n₁ ⊔ n₂ , con impl (p₁′ ∷ p₂′ ∷ []))
    convert cv d v (pi (arg _ _) (abs _ (el _ t₂))) = convert cv (suc d) v t₂
    convert cv d v (lam _ (abs _ t)) with convert cv d (suc v) t
    ...| inj₁ msg      = inj₁ msg
    ...| inj₂ (k , t') = inj₂ (k , lam t')
    convert cv d v (pat-lam _ _)     = inj₁ (unsupportedSyntax "pattern-matching lambdas")
    convert cv d v (sort _)          = inj₁ (unsupportedSyntax "sort")
    convert cv d v unknown           = inj₁ (unsupportedSyntax "unkown")

    convertChildren :
      ConvertVar → ℕ → ℕ → List (Arg AgTerm) → Error (∃[ n ] List (PsTerm n))
    convertChildren cv d v [] = inj₂ (0 , [])
    convertChildren cv d v (arg (arg-info visible _) t ∷ ts)
      with convert cv d v t | convertChildren cv d v ts
    ... | inj₁ msg      | _              = inj₁ msg
    ... | _             | inj₁ msg       = inj₁ msg
    ... | inj₂ (m , p)  | inj₂ (n , ps) with match p ps
    ... | (p′ , ps′)                      = inj₂ (m ⊔ n , p′ ∷ ps′)
    convertChildren cv d v (arg _ _ ∷ ts)   = convertChildren cv d v ts


  -- convert an Agda term to a rule-term.
  agda2term : AgTerm → Error (∃ PsTerm)
  agda2term t = convert convertVar4Term 0 0 t


  -- split a term at every occurrence of the `impl` constructor---
  -- equivalent to splitting at every occurrence of the _→_ symbol in
  -- an Agda term.
  split : ∀ {n} → PsTerm n → ∃[ k ] Vec (PsTerm n) (suc k)
  split (con impl (t₁ ∷ t₂ ∷ [])) = Prod.map suc (λ ts → t₁ ∷ ts) (split t₂)
  split t = zero , t ∷ []

  {-
  -- convert an Agda term to a goal-term, together with a `HintDB`
  -- representing the premises of the rule---this means that for a
  -- term of the type `A → B` this function will generate a goal of
  -- type `B` and a premise of type `A`.
  agda2goal×premises : AgTerm → Error (∃ PsTerm × HintDB)
  agda2goal×premises t with convert convertVar4Goal 0 t
  ... | inj₁ msg            = inj₁ msg
  ... | inj₂ (n , p)        with split p
  ... | (k , ts)            with initLast ts
  ... | (prems , goal , _)  = inj₂ ((n , goal) , toPremises 0 prems)
    where
      toPremises : ∀ {k} → ℕ → Vec (PsTerm n) k → HintDB
      toPremises i [] = []
      toPremises i (t ∷ ts) = (n , rule (rvar i) t []) ∷ toPremises (suc i) ts
  -}

  -- convert an Agda name to an rule-term.
  name2term : Name → Error (∃ PsTerm)
  name2term = agda2term ∘ unel ∘ type
    where
      unel : Type → AgTerm
      unel (el _ t) = t

  -- data-type `Exception` which is used to unquote error messages to
  -- the type-level so that `auto` can generate descriptive type-errors.

  data Exception : Message → Set where
    throw : (msg : Message) → Exception msg

  quoteError : Message → AgTerm
  quoteError (searchSpaceExhausted) = quoteTerm (throw searchSpaceExhausted)
  quoteError (unsupportedSyntax s)    = quoteTerm (throw (unsupportedSyntax s))


----------------------------
-- Some testing

  open import Data.Unit using (Unit; unit)
  open import Rel.Core.Core
  open import Rel.Core.Correflexive
  open import Rel.Core.Equality
  open import Rel.Reasoning.SubsetJudgement
  open import Rel.Reasoning.RelationJudgement renaming (begin_ to rbegin_; _∎ to _r∎)
  open import Rel.Properties
    
  sucR : Rel ℕ ℕ
  sucR = fun suc

  test : {A B : Set} → Rel ℕ ℕ → Message ⊎ (∃ PsTerm)
  test s = agda2term (quoteTerm (sucR ∙ s))

  unRight : {A B : Set} → A ⊎ B → B
  unRight (inj₁ a) = err "wtf?"
    where postulate err : {A : Set} → String → A
  unRight (inj₂ a) = a

  goalTest1 : {A B : Set}(R : Rel A B) → (R ⊆ R ∙ Id) ⇐ Unit
  goalTest1 R 
    = begin
      R ⊆ R ∙ Id
    ⇐⟨(quoteGoal g in {! agda2term (quoteTerm (R ⊆ R ∙ Id))!}) ⟩
      R ⊆ R
    ⇐⟨ (λ _ → ⊆-refl) ⟩
      Unit
    ∎

  
