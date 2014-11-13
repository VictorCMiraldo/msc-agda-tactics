

%<*NAT>
\begin{code}
data Nat : Set where
  zero : Nat
  succ : Nat -> Nat
\end{code}
%</NAT>

%<*PLUS-MUL>
\begin{code}
_+_ : Nat -> Nat -> Nat
zero     + m = m
(succ n) + m = succ (n + m)

_*_ : Nat -> Nat -> Nat
zero     * _ = zero
(succ n) * m = m + (n * m)
\end{code}
%</PLUS-MUL>

%<*TOP-BOT>
\begin{code}
data ⊤ : Set where
  tt : ⊤
  
data ⊥ : Set where

⊥-elim : {A : Set} → ⊥ → A
⊥-elim ()
\end{code}
%</TOP-BOT>

%<*UNIT>
\begin{code}
record Unit : Set where
\end{code}
%</UNIT>

%<*CONJUNCTION>
\begin{code}
data _/\_ (A B : Set) : Set where
    <_,_> : A → B → A /\ B
\end{code}
%</CONJUNCTION>

%<*DISJUNCTION>
\begin{code}
data _\/_ (A B : Set) : Set where
    inl : A → A \/ B
    inr : B → A \/ B

\/-elim : {A B C : Set} → (A → C) → (B → C) → A \/ B → C
\/-elim p₁ p₂ (inl x) = p₁ x
\/-elim p₁ p₂ (inr x) = p₂ x

\/-/\-dist : {A B C : Set} → A /\ (B \/ C) → (A /\ B) \/ (A /\ C)
\/-/\-dist < x , y > = \/-elim (λ b → inl < x , b >) (λ c → inr < x , c >) y
\end{code}
%</DISJUNCTION>

%<*IN-LIST>
\begin{code}
open import Data.List using (List; _∷_; []; _++_)

data In {A : Set} : A → List A → Set where
    InHead : {xs : List A}{y : A} → In y (y ∷ xs)
    InTail : {x : A}{xs : List A}{y : A} → In y xs → In y (x ∷ xs)
\end{code}
%</IN-LIST>


%<*inDistr-decl>
\begin{code}
inDistr : {A : Set}(l₁ l₂ : List A)(x : A)
         → In x (l₁ ++ l₂) → In x l₁ \/ In x l₂
\end{code}
%</inDistr-decl>

%<*inDistr-1>
\begin{code}
inDistr [] l₂ x prf = inr prf
\end{code}
%</inDistr-1>

%<*inDistr-2>
\begin{code}
inDistr (x ∷ l) l₂ .x InHead = inl InHead
\end{code}
%</inDistr-2>

%<*inDistr-3>
\begin{code}
inDistr (x ∷ l₁) l₂ y (InTail i) 
         = \/-elim (λ a → inl (InTail a)) inr (inDistr l₁ l₂ y i)
\end{code}
%</inDistr-3>

%<*++-assocH>
\begin{code}
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

++-assocH : ∀{a}{A : Set a}(xs ys zs : List A) →
            (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assocH [] ys zs = refl
++-assocH (x ∷ xs) ys zs =
          begin
            ((x ∷ xs) ++ ys) ++ zs
          ≡⟨ refl ⟩
            x ∷ (xs ++ ys) ++ zs
          ≡⟨ refl ⟩
            x ∷ ((xs ++ ys) ++ zs)
          ≡⟨ cong (_∷_ x) (++-assocH xs ys zs) ⟩
            x ∷ (xs ++ (ys ++ zs))
          ≡⟨ refl ⟩
            (x ∷ xs) ++ (ys ++ zs)
          ∎
\end{code}
%</++-assocH>


