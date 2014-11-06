module Util.Error where

open import Data.String using (String)

postulate
  Error : ∀{a}{A : Set a} → String → A
