module Rewr where

open import Data.Nat as N using (ℕ; zero; suc; _+_)
open import Data.String using (String)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_) renaming (proj₁ to p1; proj₂ to p2)
open import Data.Bool using (Bool; if_then_else_)

open import Data.List using (List; []; _∷_; _++_; map)

open import Reflection
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable


-- Error Handling
postulate
  error : ∀{a}{A : Set a} → String → A

--------------------------------------------------------------
-- * Applicative Maybe
--

infix 35 _<$>_
_<$>_ : ∀{a b}{A : Set a}{B : Set b}(f : A → B) → Maybe A → Maybe B
f <$> just x  = just (f x)
f <$> nothing = nothing

infixl 30 _<*>_
_<*>_ : ∀{a b}{A : Set a}{B : Set b} → Maybe (A → B) → Maybe A → Maybe B
just f  <*> m = f <$> m
nothing <*> m = nothing

fromJust : ∀{a}{A : Set a} → Maybe A → A
fromJust (just x) = x
fromJust nothing  = error "fromJust: nothing"

--
-------------------------------------------------------------
--------------------------------------------------------------
-- Term manipulation

-- Takes the term out of an el.
unEl : Type → Term
unEl (el _ x) = x

-- Takes the actual argument, ignoring argument info.
unArg : {A : Set} → Arg A → A
unArg (arg _ x) = x

mkArg : {A : Set} → A → Arg A
mkArg x = arg (arg-info visible relevant) x

-- ok, we're modeling terms with the same constructor,
-- but we also need to strip some arguments.
data TermDiff : Term → Term → Set where
  eqNone : ∀{m n}                         → TermDiff m n
  eqHead : ∀{a b x y} → x ≡ y → List Term → TermDiff (con x a) (con y b) 

-- Returns the longest common prefix of the two lists.
argsListDiff : List (Arg Term) → List (Arg Term) → List Term 
argsListDiff l1 l2 = aux (Data.List.map unArg l1) (Data.List.map unArg l2)
  where
    aux : List Term → List Term → List Term
    aux [] _ = []
    aux _ [] = []
    aux (x ∷ xs) (y ∷ ys) with x ≟ y
    ...| yes _ = x ∷ (aux xs ys)
    ...| no _  = aux xs ys

-- Traverse both terms searching for a difference. Returns the
-- quoted common part and the two different terms.
--
-- > getDiff "x:(xs ++ ys)" "x:(ys ++ xs)"
-- >  = "x:", "(xs ++ ys)", "(ys ++ xs)"
--
getDiff : (n : Term) → (m : Term) → TermDiff m n
getDiff (con x a) (con y b) with (y ≟-Name x)
...| yes f  = eqHead f (argsListDiff a b)
...| no  _  = eqNone 
getDiff n m = eqNone

-- Given a (TermDiff m n) builds up a lambda function that takes one parameter
-- and applies this difference to it.
buildCongF : {m n : Term} → TermDiff m n → Term
buildCongF eqNone       
  = error "I can't build a congruence function for such terms."
buildCongF {con n _} (eqHead f l) 
  = lam visible (con n (Data.List.map mkArg l)) 


{-
quoteTerm (λ x → 5 ∷ x)

lam visible
(con (quote _∷_)
 (arg (arg-info visible relevant) (lit (nat 5)) ∷
  arg (arg-info visible relevant) (var 0 []) ∷ []))
-}

-- Returns the terms applied to an equality.
-- If the head of the target term is not an equality, returns nothing.
getEqParts : Term → Maybe (Term × Term)
getEqParts (def (quote _≡_) (_ ∷ _ ∷ a ∷ b ∷ [])) = just (unArg a , unArg b)
getEqParts _                                      = nothing

rewrWithInternal : Term → Term → Term
rewrWithInternal f g = def (quote cong) (cf ∷ currt ∷ [])
  where
    ep : Term × Term
    ep = fromJust (getEqParts g)

    a : Term
    a = p1 ep

    b : Term
    b = p2 ep
  
    cf : Arg Term
    cf = mkArg (buildCongF (getDiff a b))

    currt : Arg Term
    currt = mkArg f 

aux1 : ℕ → ℕ → ℕ
aux1 x y = {! buildCongF (getDiff (quoteTerm (3 + (suc x))) (quoteTerm (3 + (suc y))))!}

-- quoteGoal g in let x = /* ...the clever reflection stuff */ in {! !}
-----------------------------
-----------------------------
-- Testing


open import Relation.Binary.PropositionalEquality
open import Data.List

++-assoc : ∀{a}{A : Set a}(xs ys zs : List A) → 
           (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc [] ys zs = refl
++-assoc (x ∷ xs) ys zs = cong (λ l → x ∷ l) (++-assoc xs ys zs)

++-assoc2 : ∀{a}{A : Set a}(xs ys zs : List A) → 
           (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc2 [] ys zs = refl
++-assoc2 (x ∷ xs) ys zs 
  = quoteGoal g in
    let y : _
        y = rewrWithInternal (quoteTerm (++-assoc2 xs ys zs)) g

        ep : Term × Term
        ep = fromJust (getEqParts g)

        a : Term
        a = p1 ep

        b : Term
        b = p2 ep
  
        cf : Term
        cf = buildCongF (getDiff a b)

        currt : Term
        currt = quoteTerm (++-assoc2 xs ys zs) 

        z : Term
        z =  def (quote cong) (mkArg cf ∷ mkArg currt ∷ [])
    in {!g  !}

++-neutral : ∀{a}{A : Set a}(xs : List A)
           → xs ++ [] ≡ xs
++-neutral [] = refl
++-neutral (x ∷ xs) = cong (λ l → x ∷ l) (++-neutral xs)

++-neutral2 : ∀{a}{A : Set a}(xs : List A)
           → xs ++ [] ≡ xs
++-neutral2 [] = refl
++-neutral2 (x ∷ xs)
  = quoteGoal g in
    let y : _
        y = rewrWithInternal (quoteTerm (++-neutral2 xs)) g

        ep : Term × Term
        ep = fromJust (getEqParts g)

        a : Term
        a = p1 ep

        b : Term
        b = p2 ep
  
        cf : Term
        cf = buildCongF (getDiff a b)

        currt : Term
        currt = quoteTerm (++-neutral2 xs) 

        z : Term
        z =  def (quote cong) (mkArg cf ∷ mkArg currt ∷ [])
    in {!g  !}
