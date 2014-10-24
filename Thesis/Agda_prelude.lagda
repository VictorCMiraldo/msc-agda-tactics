Although functional languages have been receiving great attention
and a fast evolution in recent years, one of the biggest jumps
have been the introduction of dependent types. Agda\cite{norell07} is one of such languages, with some other 
big names beeing \emph{Epigram} \cite{mcbride05} and \emph{Coq} \cite{bertot06}. 

In languages like Haskell or ML, where a Hindley-Milner based algorihm is used
for type checking, values and types are clearly separated. Within dependent
types, though, the story changes. A type can depend on any value the programmer
whishes for. A classical example are the fixed size vectors \inlagda{Vec A n}, where \inlagda{A}
is the type of the elements and \inlagda{n} is the length of the vector. The reader familiar
with C may think: but I also hve fixed size arrays in C. The difference is that
this \inlagda{n} need not to be known at compile time, it can be an arbitrary term (as long
as it has type \inlagda{Nat}). That is, there is difference between types and values,
they are all sets, as shall see in chapter \ref{chap:martinlof}).

In this chapter I'll introduce the basics of Agda and show some examples in both
the programming and the proof theoretic sides of the language. Later on, in 
chapter \ref{chap:martinlof}, we will see the theory in which Agda is built 
on top of, and a lot of concepts introduced here will become clearer. 
Some background on the $\lambda$-calculus and the Curry-Howard isomorphism is
presented in section \ref{sec:background:lambdacalculus}.

\subsection{Some Programming Examples}

In terms of programing, Agda and Haskell are very close. Agda's syntax was
inspired by Haskell and, beeing also a functional language, a lot of
the programming techniques we need to use in Haskell also apply for an Agda program.
Knowledge of Haskell is not strictly necessary, but of a great value for a better
understanting of Agda.\\

The cannonical example is to encode Peano's Natural numbers:\\
\begin{agdacode}
\begin{code}
data Nat : Set where
  zero : Nat
  succ : Nat -> Nat
\end{code}
\end{agdacode}

The data declarations in Agda are very similar to a GADTs\footnote{
%%%% BEGIN FOOTNOTE
Generalized Algebraic Data Types
\begin{TODO}
  \item cite this?
\end{TODO}
%%%% END FOOTNOTE
} in Haskell. Remember that in Agda types and values are the same thing, 
in this data declaration we're stating that \inlagda{Nat} is \emph{of type} 
\inlagda{Set}. This \inlagda{Set} is the type of types, later on we'll
see it's formal definition and why it is needed. For now, think of it
as Haskell's $*$ kind.\\

As it was expected, definitions are made by structural induction over the
data type. Pattern matching is the mechanism of choice here.\\
\begin{agdacode}
\begin{code}
_+_ : Nat -> Nat -> Nat
zero     + m = m
(succ n) + m = succ (n + m)

_*_ : Nat -> Nat -> Nat
zero     * _ = zero
(succ n) * m = m + (n * m)
\end{code}
\end{agdacode}

There are a few points of interest in the above definitions. The underscore pattern
(\_) has the same meaning as in Haskell, it matches anything. The underscore in
the symbol name, though, indicates where the parameters should be relative to the symbol name. 
Agda supports mixfix operators and has full UTF8 support. It is possible to
apply a mixfix operator in normal infix form: \inlagda{a + b = \_+\_ a b}.


