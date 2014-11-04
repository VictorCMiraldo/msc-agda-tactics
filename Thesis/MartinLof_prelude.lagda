Type theory was originally developed with the goal of beeing a clarification, or basis,
for constructive Mathematics, but, unlike most other formalizations of mathematics, it is
not based on first order logic. Therefore, we need to introduce the symbols and
rules we'll use before presenting the theory itself. The heart of this interpretation of
proofs as programs is the Curry-Howard isomorphism, explained in section \ref{sec:background:lambdacalculus}.

Martin-L\"{o}f's theory of types \cite{lof84} is an extension of regular type theory. This extended
interpretation includes universal and existential quantification. 
A proposition is interpreted as a set whose elements
are proofs of such proposition. Therefore, true proposition is a non-empty set and a false proposition
is a empty set, meaning that there is no proof for such proposition. Apart from \emph{sets as propositions},
we can look at sets from a \emph{specification} angle, and this is the most insteresting view for programming.
A given element $a$ of a set $A$ can be viewed as: a proof for proposition $A$; a program satisfying the
specification $A$; or even a solution to problem $A$.

In this chapter we'll explain the basics of the theory of types (in it's \emph{intensional} variation)
trying to estabilish connections with the Agda language. We'll begin by providing some basic notions
and the interpretation of propositional logic into set theory. We'll follow with the notion of arity,
which differs from it's canonical meaning, finishing with a small discussion on the dependent product
and sums operators, which closes the gap to first order logic. The interested reader should continue
with \cite{nords90} or, for a more practical view, \cite{wouter08,bove2009}

\section{Propositions as Sets}
\label{sec:martinlof:propositionsassets}

In classical mathematics, a proposition is thought of as beeing either true or false, it doesn't
matter if we can prove or disprove it. On a different angle, a proposition is constructively true
if we have a \emph{method} for proving it. A classical example is the law of excluded middle, $A \vee \neg A$,
which is trivialy true since $A$ can only be true or false. Constructively, though, a method for proving a disjunction
must prove that one of the disjuncts holds. Since we cannot prove an arbitrary proposition $A$, we have
no proof for $A \vee \neg A$. 

Therefore, we have that the constructive explanation of propositions is built in terms of proofs, and
not an indedendent mathematical object. 

\paragraph{Absurd,} $\bot$, is identified with the empty set, $\emptyset$. That is, a set with no elements
or a proposition with no proof.

\paragraph{Implication,} $A \supset B$ is viewed as the set of functions from $A$ to $B$, denoted $B^A$. That is,
a proof of $A \supset B$ is a function that, given a proof of $A$, returns a proof of $B$.

\newcommand{\pone}{\pi_1}
\newcommand{\ptwo}{\pi_2}
\paragraph{Conjunction,} $A \wedge B$ is identified with the cartesian product $A \times B$. That is, a proof
of $A \wedge B$ is a pair whose first component is a proof of $A$ and second component is a proof of $B$.
Let us denote the first and second projections of a given pair by $\pone$ and $\ptwo$.
The elements of $A \times B$ are of the form $(a, b)$, where $a \in A$ and $b \in B$.

\newcommand{\ione}{i_1}
\newcommand{\itwo}{i_2}
\paragraph{Disjunction,} $A \vee B$, is identified with the disjoint union $A + B$. A proof
of $A \vee B$ is either a proof of $A$ or a proof of $B$. The elements of $A + B$ are of the
form $\ione\; a$ and $\itwo\; b$ with $a \in A$ and $b \in B$.

\paragraph{Negation,} $\neg A$, can be identified relying on it's definition
on the minimal logic, $A \supset \bot$









%Type theory provides us with derivational rules to discuss the validity of judgements of
%the following form:
%
%\begin{enumerate}[i)]
%  \item $A$ is a set.
%  \item $A$ and $B$ are equal sets.
%  \item $a$ is an element of a set $A$.
%  \item $a$ and $b$ are equal elements of a set $A$.
%\end{enumerate}


