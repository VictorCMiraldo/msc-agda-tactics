module Error where

open import Data.List
open import Data.Nat
open import Data.String using (String)
open import Reflection

postulate
  error : ∀{a}{A : Set a} → String → A

head : ∀{a}{A : Set a} → List A → A
head [] = error "Head"
head (x ∷ _) = x

-- Trying to get the type of a context variable
-- raises an "internal error" at TypeChecking/Reduce/Monad.hs:163.
--
-- To reproduce, put cursor on hole 0 and C-c C-n.
--
ctxtest1 : ∀{a}{A : Set a} → ℕ → List A → A
ctxtest1 n l = quoteContext e in {!type (head e)!}
