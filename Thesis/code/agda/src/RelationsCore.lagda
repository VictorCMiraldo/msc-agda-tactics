\begin{code}
open import Data.Sum using (_⊎_)
open import Data.Product using (_×_; ∃; _,_; proj₂; proj₁)
open import Data.Sum using (_⊎_; [_,_]) renaming (inj₁ to i1; inj₂ to i2; [_,_]′ to case)
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

%<*composition-naive>
\begin{code}
_after_ : {A B C : Set} → Rel B C → Rel A B → Rel A C
R after S = λ c a → ∃ (λ b → R c b × S b a)
\end{code}
%</composition-naive>

%<*composition-final>
\begin{code}
record _∙_ {A B C : Set}(R : Rel B C)(S : Rel A B)(c : C)(a : A) : Set
  where
    constructor _,_
    field
      witness  : B
      composes : (R c witness) × (S witness a)
\end{code}
%</composition-final>

%<*product-final>
\begin{code}
record ⟨_,_⟩ {A B C : Set}(R : Rel A B)(S : Rel A C)(bc : B × C)(a : A) : Set
  where constructor cons-⟨,⟩
        field un : (R (proj₁ bc) a) × (S (proj₂ bc) a)
\end{code}
%</product-final>

\begin{code}
p1∙ : {A B C : Set}{R : Rel B C}{S : Rel A B}{c : C}{a : A} → (R ∙ S) c a → B
p1∙ rs = _∙_.witness rs

p2∙ : {A B C : Set}{R : Rel B C}{S : Rel A B}{c : C}{a : A}(prf : (R ∙ S) c a) → (R c (p1∙ prf)) × (S (p1∙ prf) a)
p2∙ rs = _∙_.composes rs

π₁ : {A B : Set} → Rel (A × B) A
π₁ a ab = fun proj₁ a ab

π₂ : {A B : Set} → Rel (A × B) B
π₂ b ab = fun proj₂ b ab
\end{code}

%<*product-univ-r1>
\begin{code}
prod-uni-r1 : ∀{A B C} → {X : Rel C (A × B)}
             → (R : Rel C A) → (S : Rel C B)
             → X ⊆ ⟨ R , S ⟩
             → π₁ ∙ X ⊆ R
\end{code}
%</product-univ-r1>
\begin{code}
prod-uni-r1 {X = X} r s (⊆in prf)
  = ?
\end{code}
%<*product-univ-r2>
\begin{code}
prod-uni-r2 : ∀{A B C} → {X : Rel C (A × B)}
            → (R : Rel C A) → (S : Rel C B)
            → X ⊆ ⟨ R , S ⟩
            → π₂ ∙ X ⊆ S
\end{code}
%</product-univ-r2>
\begin{code}            
prod-uni-r2 = ?
\end{code}
%<*product-univ-l>
\begin{code}
prod-uni-l : ∀{A B C} → {X : Rel C (A × B)}
           → (R : Rel C A) → (S : Rel C B)
           → (π₁ ∙ X) ⊆ R → (π₂ ∙ X) ⊆ S
           → X ⊆ ⟨ R , S ⟩
\end{code}
%</product-univ-l>
\begin{code}           
prod-uni-l {X = X} r s pr ps 
  = ?
\end{code}


%<*coproduct-final>
\begin{code}
record either {A B C : Set}(R : Rel A C)(S : Rel B C)(c : C)(ab : A ⊎ B) : Set
  where constructor cons-either
        field un : case (R c) (S c) ab
\end{code}
%</coproduct-final>

\begin{code}
ι₁ : {A B : Set} → Rel A (A ⊎ B)
ι₁ = fun i1

ι₂ : {A B : Set} → Rel B (A ⊎ B)
ι₂ = fun i2
\end{code}

%<*coproduct-uni-r1>
\begin{code}
coprod-uni-r1 : ∀{A B C}{X : Rel (A ⊎ B) C}
              → (R : Rel A C) → (S : Rel B C)
              → (X ≡r either R S) 
              → R ≡r X ∙ ι₁
\end{code}
%</coproduct-uni-r1>
\begin{code}
coprod-uni-r1 = ?
\end{code}

%<*coproduct-uni-r2>
\begin{code}
coprod-uni-r2 : ∀{A B C}{X : Rel (A ⊎ B) C}
              → (R : Rel A C) → (S : Rel B C)
              → (X ≡r either R S) 
              → S ≡r X ∙ ι₂
\end{code}
%</coproduct-uni-r2>
\begin{code}
coprod-uni-r2 = ?
\end{code}

%<*coproduct-uni-l>
\begin{code}
coprod-uni-l : ∀{A B C}{X : Rel (A ⊎ B) C}
             → (R : Rel A C) → (S : Rel B C)
             → (R ≡r X ∙ ι₁) → (S ≡r X ∙ ι₂)
             → X ≡r either R S
\end{code}
%</coproduct-uni-l>
\begin{code}
coprod-uni-l = ?
\end{code}

