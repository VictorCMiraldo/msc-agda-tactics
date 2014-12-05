\begin{code}
open import Data.Sum using (_⊎_)
open import Data.Product using (_×_)
open import Relation.Binary.PropositionalEquality using (_≡_)
\end{code}


%<*subset-def>
\begin{code}
ℙ : Set → Set1
ℙ A = A → Set
\end{code}
%</subset-def>

%<*relation-def>
\begin{code}
Rel : Set → Set → Set1
Rel A B = B → A → Set
\end{code}
%</relation-def>

\begin{code}
infix 8 _∪_ _∩_
\end{code}

%<*first-constructs>
\begin{code}
_∪_ : {A B : Set} → Rel A B → Rel A B → Rel A B
(R ∪ S) b a = R b a ⊎ S b a

_∩_ : {A B : Set} → Rel A B → Rel A B → Rel A B
(R ∩ S) b a = R b a × S b a

fun : {A B : Set} → (A → B) → Rel A B
fun f b a = f a ≡ b
\end{code}
%</first-constructs>
