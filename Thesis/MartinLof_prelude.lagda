Type theory was originally developed with the goal of beeing a clarification, or basis,
for constructive Mathematics, but, unlike most other formalizations of mathematics, it is
not based on first order logic. The heart of this interpretation is the Curry-Howard isomorphism.
This result introduces an isomorphism between type derivations (or, typeable Haskell programs)
and propositional logic.

Martin-L\"{o}f's theory of types is an extension of regular type theory, it extends this
interpretation to include quantification. A proposition is interpreted as a set whose elements
are proofs of such proposition. Therefore, true proposition is a non-empty set and a false proposition
is a empty set, meaning that there is no proof for such proposition. Apart from \emph{sets as propositions},
we can look at sets from a \emph{specification} angle, and this is the most insteresting view for programming.

Type theory provides us with derivational rules to discuss the validity of judgements of
the following form:
\begin{enumerate}[i)]
  \item $A$ is a set.
  \item $A$ and $B$ are equal sets.
  \item $a$ is an element of a set $A$.
  \item $a$ and $b$ are equal elements of a set $A$.
\end{enumerate}
\cite{nords90}

