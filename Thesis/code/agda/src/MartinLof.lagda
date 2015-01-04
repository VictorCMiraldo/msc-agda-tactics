%<*proof>
\begin{code}
data Bool : Set where
  tt : Bool
  ff : Bool

if_then_else_ : {A : Set} → Bool → A → A → A
if tt then x else _ = x
if ff then _ else x = x

data Id (A : Set)(x : A) : A → Set where
  id : (a : A) → Id A x a

proof : {A : Set}{a : A}{b : Bool} → Id A (if b then a else a) a
proof {a = a} {b = tt} = id a
proof {a = a} {b = ff} = id a
\end{code}
%</proof>
