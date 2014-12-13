\begin{code}
open import Data.Sum using (_⊎_)
open import Data.Product using (_×_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Function using (id; flip)
\end{code}


%<*subset-def>
\begin{code}
ℙ : Set → Set1
ℙ A = A → Set
\end{code}
%</subset-def>

\begin{code}
infix 8 _∪_ _∩_
\end{code}

%<*relation-def>
\begin{code}
Rel : Set → Set → Set1
Rel A B = B → A → Set

_∪_ : {A B : Set} → Rel A B → Rel A B → Rel A B
(R ∪ S) b a = R b a ⊎ S b a

_∩_ : {A B : Set} → Rel A B → Rel A B → Rel A B
(R ∩ S) b a = R b a × S b a

fun : {A B : Set} → (A → B) → Rel A B
fun f b a = f a ≡ b
\end{code}
%</relation-def>

\begin{code}
infix 6 _≡r_ _⊆_
\end{code}

%<*subrelation>
\begin{code}
data _⊆_ {A B : Set}(R S : Rel A B) : Set where
  ⊆in : (∀ a b → R b a → S b a) → R ⊆ S
\end{code}
%</subrelation>

%<*releq>
\begin{code}
record _≡r_ {A B : Set}(R S : Rel A B) : Set where
  constructor _,_
  field
    p1 : R ⊆ S
    p2 : S ⊆ R
\end{code}
%</releq>

%<*releq-is-not-propeq>
\begin{code}
postulate
  rel-ext : {A B : Set}{R S : Rel A B}
          → (∀ b a → R b a ≡ S b a)
          → R ≡ S

naive₁ : {A B : Set}{R S : Rel A B}
       → R ⊆ S → S ⊆ R → R ≡ S
naive₁ (⊆in rs) (⊆in sr) 
  = rel-ext (λ b a → ? )
\end{code}
%</releq-is-not-propeq>

%<*releq-lifting>
\begin{code}
≡r-promote : {A B : Set}{R S : Rel A B}
             → R ≡r S → R ≡ S
≡r-promote {R = R} {S = S} (⊆in rs , ⊆in sr)
  = Λ-ext (λ a → ℙ-ext (flip R a) (flip S a) (rs a) (sr a))
  where
    Λ_ : {A B : Set}(R : Rel A B) → A → ℙ B
    Λ R = λ a b → R b a 

    postulate
      Λ-ext : {A B : Set}{R S : Rel A B}
            → (∀ a → (Λ R) a ≡ (Λ S) a)
            → R ≡ S

      ℙ-ext : {A : Set}(s1 s2 : ℙ A)
            → (∀ x → s1 x → s2 x)
            → (∀ x → s2 x → s1 x)
            → s1 ≡ s2    
\end{code}
%</releq-lifting>
