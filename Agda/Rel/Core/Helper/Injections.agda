open import Rel.Core

module Rel.Core.Helper.Injections where

  i1-inj : ∀{a b}{A : Set a}{B : Set b}{x y : A} 
         → i1 {b = b} {B = B} x ≡ i1 y → x ≡ y
  i1-inj refl = refl

  i2-inj : ∀{a b}{A : Set a}{B : Set b}{x y : B} 
         → i2 {a = a} {A = A} x ≡ i2 y → x ≡ y
  i2-inj refl = refl

  
