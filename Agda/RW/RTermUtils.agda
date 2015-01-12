open import Prelude
open import Data.Nat.Properties.Simple
open import Data.Fin.Properties
open import Category.Monad using (module RawMonad)
open import Data.Maybe using (Maybe; just; nothing) renaming (monad to monadMaybe)
open import Relation.Binary.PropositionalEquality using (inspect; [_])

import RTerm

module RTermUtils
  (Name : Set) (_≟-Name_ : (x y : Name) → Dec (x ≡ y))
  (Lit  : Set) (_≟-Lit_  : (x y : Lit)  → Dec (x ≡ y))
  where

  open RawMonad {{...}} using (_<$>_; _>>=_; return)

  private
    instance
      MaybeMonad = monadMaybe

  open RTerm Name _≟-Name_ Lit _≟-Lit_
  open Inject {{...}}
  open Raise {{...}}

  private
    -- Utilities to work with Fin's
    useLast : ∀ o → Fin (o + 1)
    useLast o rewrite +-suc o zero 
                    | +-right-identity o 
                    = fromℕ o

    i+1≡suci : ∀{i o} → RTerm (i + 1) o → RTerm (suc i) o
    i+1≡suci {i} rt rewrite +-comm i 1 = rt

    o+1≡suco : ∀{i o} → RTerm i (o + 1) → RTerm i (suc o)
    o+1≡suco {_} {o} rt rewrite +-comm o 1 = rt

  -- Term Intersection.
  --   Given two terms, for instance (x ∷ a) and (x ∷ b)
  --   returns a (_∷_ x 0); where 0 denotes a new ovar.
  --
  -- Term intersection can be too general, though.
  -- Let's consider:
  --    x ∷ ((xs ++ ys) ++ zs) ∩ x ∷ (xs ++ (ys ++ zs))
  --    == x ∷ (1 ++ 0)
  --
  -- Here we have two ovar's, denoting where the terms did differ.
  -- For this reason we provide a ∩', which will only keep a constructor
  -- if both terms share a common argument to such constructor.
  mutual 
    _∩_ : ∀{i o} → RTerm i o → RTerm i o → ∃ (λ n → RTerm i (o + n))
    _∩_ {i} {o} (rcon s₁ a₁) (rcon s₂ a₂) with s₁ ≟-Name s₂
    ...| no  _ = 1 , ovar (useLast o)
    ...| yes _ with a₁ ∩* a₂
    ...| n , a' = n , rcon s₁ a'
    _∩_ {i} {o} (ivar x) (ivar y) with x ≟-Fin y
    ...| yes _ = 0 , ivar x
    ...| no _  = 1 , ovar (useLast o)
    _∩_ {i} {o} (ovar x) (ovar y) with x ≟-Fin y
    ...| yes _ = 0 , ovar (subst Fin (sym (+-right-identity o)) x)
    ...| no _  = 1 , ovar (useLast o)
    _∩_ {i} {o} (rlit x) (rlit y) with x ≟-Lit y
    ...| yes _ = 0 , rlit x
    ...| no  _ = 1 , ovar (useLast o)
    _∩_ {i} {o} (rlam x) (rlam y) with x ∩ y
    ...| n , x' = n , rlam x'
    _∩_ {i} {o} _ _ = 1 , ovar (useLast o)

    _∩*_ : ∀{i o} → List (RTerm i o) → List (RTerm i o) → ∃ (λ n → List (RTerm i (o + n)))
    _∩*_ [] []             = 0 , []
    _∩*_ {i} {o} (a ∷ as) (b ∷ bs) with a ∩ b | as ∩* bs
    ...| n , a' | m , as' 
      = n + m , assocRs {i} {o} {n} {m} (raise m a') 
              ∷ map (assocTl {i} {o} ∘ inject n) as'
      where
        assocRs : ∀{i o n m} → RTerm i (m + (o + n)) → RTerm i (o + (n + m))
        assocRs {i} {o} {n} {m} rt 
          rewrite +-comm m (o + n)
                | +-assoc o n m
                = rt

        assocHd : ∀{i o n m} → RTerm i (o + n + m) → RTerm i (o + (n + m))
        assocHd {i} {o} {n} {m} rt rewrite +-assoc o n m = rt

        assocTl : ∀{i o n m} → RTerm i ((o + m) + n) → RTerm i (o + (n + m))
        assocTl {i} {o} {n} {m} rt rewrite +-assoc o n m
                                         | +-comm n m 
                                         = assocHd {i} {o} {m} {n} rt
    _∩*_ _ _
      = diferentArities
      where postulate diferentArities : ∀{a}{A : Set a} → A

  -- Term Head Difference;
  --
  --   Strips the head of both RTerm's as long as they have the same constructor at their heads.
  --   Returns both the constructor and the respective argument list.
  stripEqHead : ∀{i o} → RTerm i o → RTerm i o → Maybe (Name × List (RTerm i o) × List (RTerm i o))
  stripEqHead (rcon s₁ a₁) (rcon s₂ a₂) with s₁ ≟-Name s₂
  ...| yes _ = just (s₁ , a₁ , a₂)
  ...| no  _ = nothing
  stripEqHead _ _ = nothing

  -- Term Erase;
  --
  --  Erases (subtracts) the second term from the first one. Upon successful erasing will
  --  return a term with a new ovar, representing the hole just created.
  mutual
    {-# TERMINATING #-}
    _-_ : ∀{i o} → RTerm i o → RTerm i o → Maybe (RTerm i (suc o))
    _-_ {i} {o} t₁ t₂ with t₁ ≟-RTerm t₂ 
    ...| yes _ = just (ovar (fromℕ o))
    ...| no  _ with t₁ 
    ...| (rcon s a) = (rcon s) <$> (a -* t₂)
    ...| (rlam t)   = rlam     <$> t - i+1≡suci (injectInternal 1 t₂)
    ...| _          = nothing 

    _-*_ : ∀{i o} → List (RTerm i o) → RTerm i o → Maybe (List (RTerm i (suc o)))
    _-*_         []       _ = nothing
    _-*_ {i} {o} (a ∷ as) t with a ≟-RTerm t
    ...| yes _ = just (ovar (fromℕ o) ∷ (map (o+1≡suco ∘ inject 1) as))
    ...| no  _ = (_∷_ (o+1≡suco (inject 1 a))) <$> as -* t 

  {-
  -- Will only maintain constructors that have at least one ivar applied to it.
  -- linearize (x ∷ (0 ++ 1)) would yield (x ∷ 0)
  mutual
    linearize : ∀{i o} → RTerm i o → RTerm i o
    linearize rt = {!!}

    linearize* : ∀{i o} → List (RTerm i o) → List (RTerm i o)
    linearize* = {!!}
  -}
