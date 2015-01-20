open import Function using (_∘_)
open import Data.Nat using (ℕ; suc; zero; _+_; _≤_) renaming (_≟_ to _≟-ℕ_)
open import Data.Nat.Show renaming (show to showℕ)
open import Data.Nat.Properties.Simple using (+-suc; +-comm)
open import Data.Fin using (Fin; toℕ) renaming (inject+ to finject; raise to fraise; zero to fzero; suc to fsuc)
open import Data.Fin.Properties as FinProps renaming (_≟_ to _≟-Fin_)
open import Data.Maybe using (Maybe; just; nothing) renaming (monad to monadMaybe)
open import Data.List as List using (List; _∷_; []; map)
open import Data.List.Properties as ListProps renaming (∷-injective to ∷-inj)
open import Data.String using (String) renaming (_++_ to _++s_)
open import Data.Product as Prod using (∃; _×_; _,_) renaming (proj₁ to p1; proj₂ to p2)
open import Category.Monad using (module RawMonad)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl; cong; sym)

open import RWUtils

module RTerm
  (Name : Set) (_≟-Name_ : (x y : Name) → Dec (x ≡ y))
  (Lit  : Set) (_≟-Lit_  : (x y : Lit)  → Dec (x ≡ y))
  where

  open RawMonad {{...}} using (_<$>_; _>>=_; return)

  private
    instance
      MaybeMonad = monadMaybe

  -- Finite Terms with internal abstractions.
  -- The type 'RTerm 3 5' represents a term with
  -- three internal lambda-abstractions and
  -- five variables defined somewhere else.
  data RTerm (i o : ℕ) : Set where
    ivar : (x : Fin i) → RTerm i o
    ovar : (x : Fin o) → RTerm i o
    rcon : (s : Name) (ts : List (RTerm i o)) → RTerm i o
    rlit : (l : Lit) → RTerm i o
    rlam : RTerm (suc i) o → RTerm i o
    
  -- Declaring the equality rules induced by our constructors.

  ivar-inj : ∀{i o x y} 
           → ivar {i} {o} x ≡ ivar {i} {o} y
           → x ≡ y
  ivar-inj refl = refl

  ovar-inj : ∀{i o x y} 
           → ovar {i} {o} x ≡ ovar {i} {o} y
           → x ≡ y
  ovar-inj refl = refl

  rcon-inj : ∀{i o c₁ c₂ t₁ t₂}
           → rcon {i} {o} c₁ t₁ ≡ rcon {i} {o} c₂ t₂
           → c₁ ≡ c₂ × t₁ ≡ t₂
  rcon-inj refl = (refl , refl)

  rlit-inj : ∀{i o x y}
           → rlit {i} {o} x ≡ rlit {i} {o} y
           → x ≡ y
  rlit-inj refl = refl

  rlam-inj : ∀{i o m n}
           → rlam {i} {o} m ≡ rlam {i} {o} n
           → m ≡ n
  rlam-inj refl = refl

  showRTerm : ∀{i o} 
            → (Name → String) 
            → (Lit  → String)
            → RTerm i o → String
  showRTerm {i} showName showLit rt 
    = makeλ i ++s show rt
    where
      makeλ : ℕ → String
      makeλ zero = ""
      makeλ (suc n) = "λ" ++s makeλ n
      
      mutual
        show : ∀{i o} → RTerm i o → String
        show (ivar x) = showℕ (toℕ x) ++s "^"
        show (ovar x) = showℕ (toℕ x)
        show (rcon s ts) = "(" ++s showName s ++s " " ++s showArgs ts ++s ")"
        show (rlit l) = showLit l
        show (rlam tr) = "(λ." ++s show tr ++s ")"

        showArgs : ∀{i o} → List (RTerm i o) → String
        showArgs []       = ""
        showArgs (s ∷ ss) = show s ++s " " ++s showArgs ss 

  mutual 
    _≟-RTerm_ : ∀{i o} → (t₁ t₂ : RTerm i o) → Dec (t₁ ≡ t₂)
    _≟-RTerm_ (ivar v₁) (ivar v₂) with v₁ ≟-Fin v₂
    ...| yes tt = yes (cong ivar tt)
    ...| no  ff = no (ff ∘ ivar-inj)
    _≟-RTerm_ (ovar v₁) (ovar v₂) with v₁ ≟-Fin v₂
    ...| yes tt = yes (cong ovar tt)
    ...| no  ff = no (ff ∘ ovar-inj)
    _≟-RTerm_ (rcon c₁ t₁) (rcon c₂ t₂) with c₁ ≟-Name c₂
    ...| no  ff = no (ff ∘ p1 ∘ rcon-inj)
    ...| yes tt rewrite tt with t₁ ≟-RTerms t₂
    ...| no  fft = no (fft ∘ p2 ∘ rcon-inj)
    ...| yes ttt = yes (cong (rcon c₂) ttt) 
    _≟-RTerm_ (rlit l₁) (rlit l₂) with l₁ ≟-Lit l₂
    ...| yes tt = yes (cong rlit tt)
    ...| no  ff = no (ff ∘ rlit-inj)
    _≟-RTerm_ (rlam t₁) (rlam t₂) with t₁ ≟-RTerm t₂
    ...| yes tt = yes (cong rlam tt)
    ...| no  ff = no (ff ∘ rlam-inj)
    _≟-RTerm_ (ivar _)   (ovar _)   = no (λ ())
    _≟-RTerm_ (ivar _)   (rlit _)   = no (λ ())
    _≟-RTerm_ (ivar _)   (rlam _)   = no (λ ())
    _≟-RTerm_ (ivar _)   (rcon _ _) = no (λ ())
    _≟-RTerm_ (ovar _)   (ivar _)   = no (λ ())
    _≟-RTerm_ (ovar _)   (rlit _)   = no (λ ())
    _≟-RTerm_ (ovar _)   (rlam _)   = no (λ ())
    _≟-RTerm_ (ovar _)   (rcon _ _) = no (λ ())
    _≟-RTerm_ (rlit _)   (ivar _)   = no (λ ())
    _≟-RTerm_ (rlit _)   (ovar _)   = no (λ ())
    _≟-RTerm_ (rlit _)   (rlam _)   = no (λ ())
    _≟-RTerm_ (rlit _)   (rcon _ _) = no (λ ())
    _≟-RTerm_ (rlam _)   (ovar _)   = no (λ ())
    _≟-RTerm_ (rlam _)   (ivar _)   = no (λ ())
    _≟-RTerm_ (rlam _)   (rlit _)   = no (λ ())
    _≟-RTerm_ (rlam _)   (rcon _ _) = no (λ ())
    _≟-RTerm_ (rcon _ _) (ovar _)   = no (λ ())
    _≟-RTerm_ (rcon _ _) (rlit _)   = no (λ ())
    _≟-RTerm_ (rcon _ _) (rlam _)   = no (λ ())
    _≟-RTerm_ (rcon _ _) (ivar _)   = no (λ ())

    _≟-RTerms_ : ∀{i o} → (ts₁ ts₂ : List (RTerm i o)) → Dec (ts₁ ≡ ts₂)
    _≟-RTerms_ [] []      = yes refl
    _≟-RTerms_ [] (_ ∷ _) = no (λ ())
    _≟-RTerms_ (_ ∷ _) [] = no (λ ())
    _≟-RTerms_ (x ∷ xs) (y ∷ ys) with x ≟-RTerm y
    ...| no  ff = no (ff ∘ p1 ∘ ∷-inj)
    ...| yes tt rewrite tt with xs ≟-RTerms ys
    ...| yes tts = yes (cong (_∷_ y) tts)
    ...| no  ffs = no (ffs ∘ p2 ∘ ∷-inj)

  -- applies (fraise 1) to all internal variables.
  {-# TERMINATING #-}
  raiseInternal : ∀{i o} (n : ℕ) → RTerm i o → RTerm (n + i) o
  raiseInternal n (ivar x) = ivar (fraise n x)
  raiseInternal n (ovar x) = ovar x
  raiseInternal n (rcon s ts) = rcon s (map (raiseInternal n) ts)
  raiseInternal n (rlit l) = rlit l
  raiseInternal {i} n (rlam t) with raiseInternal n t
  ...| t' rewrite +-suc n i = rlam  t'

  {-# TERMINATING #-}
  injectInternal : ∀{i o} (n : ℕ) → RTerm i o → RTerm (i + n) o
  injectInternal n (ivar x) = ivar (finject n x)
  injectInternal _ (ovar x) = ovar x
  injectInternal n (rcon s ts) = rcon s (map (injectInternal n) ts)
  injectInternal _ (rlit l) = rlit l
  injectInternal {i} n (rlam t) with injectInternal n t
  ...| t' = rlam t'

  replace : ∀{i o₁ o₂} → (Fin o₁ → RTerm i o₂) 
          → RTerm i o₁ → RTerm i o₂
  replace f (ovar x) = f x
  replace {i} f (rlam t) = rlam (replace (raiseInternal 1 ∘ f) t)
  replace _ (ivar x) = ivar x
  replace _ (rlit l) = rlit l
  replace f (rcon s ts) = rcon s (replace' f ts)
    where
      replace' : ∀{i o₁ o₂} → (Fin o₁ → RTerm i o₂)
               → List (RTerm i o₁) → List (RTerm i o₂)
      replace' f []       = []
      replace' f (x ∷ xs) = replace f x ∷ replace' f xs

  -- Replacement composition
  _◇_ : ∀{i o₁ o₂ o₃} 
      → (Fin o₂ → RTerm i o₃)
      → (Fin o₁ → RTerm i o₂)
      → Fin o₁ → RTerm i o₃
  f ◇ g = replace f ∘ g

    -- type class for injections in the fashion of Fin.inject+
  record Inject (T : ℕ → Set) : Set where
    constructor inj
    field
      inject : ∀ {m} n → T m → T (m + n)

    inject≤ : ∀ {m n} → m ≤ n → T m → T n
    inject≤ {m} {n} p t = P.subst T (sym (Δ-correct p)) (inject (Δ p) t)

  open Inject {{...}} using (inject; inject≤)


  -- type class for raising in the fashion of Fin.raise
  record Raise (T : ℕ → Set) : Set where
    constructor rai
    field
      raise : ∀ {m} n → T m → T (n + m)

    raise≤ : ∀ {m n} → m ≤ n → T m → T n
    raise≤ {m} {n} p t = P.subst T (sym (P.trans (Δ-correct p) (+-comm m (Δ p)))) (raise (Δ p) t)

  open Raise {{...}} using (raise; raise≤)

  instance
    InjectFin : Inject Fin
    InjectFin = inj finject

    RaiseFin : Raise Fin
    RaiseFin = rai fraise

    InjectRTerm : ∀{i} → Inject (RTerm i)
    InjectRTerm = inj (λ n → replace (ovar ∘ inject n))

    RaiseRTerm : ∀{i} → Raise (RTerm i)
    RaiseRTerm = rai (λ n → replace (ovar ∘ raise n))

    InjectRTerms : ∀{i} → Inject (List ∘ RTerm i)
    InjectRTerms = inj (λ n → map (inject n))

    RaiseRTerms : ∀{i} → Raise (List ∘ RTerm i)
    RaiseRTerms = rai (λ n → map (raise n))
