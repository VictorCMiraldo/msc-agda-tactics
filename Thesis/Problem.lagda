As we could see in section \ref{sec:prelude:agdalanguage}, Agda is a very expressive language
and it allows us to build smaller proofs than the great majority of proof assistants available.
The mixfix feature gives the language a very customizable feel, one application is the
equational reasoning framework. In the following illustration we prove the associativity of
the concatenation operation.

\begin{agdacode}
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
\end{agdacode}

The notation is very clear and understandable, it indeed looks very much
to what a \emph{squiggolist}\footnote{
%%%% BEGIN FOOTNOTE
\emph{Squiggol} is a slang name for the Bird–Meertens formalism, due to the squiggly symbols it
uses.
%%%% END FOOTNOTE
} would write on paper. One of the main downsides to it, which is also inherent to Agda in general,
is the need to specify every single detail of the demonstration, even the trivial ones.
