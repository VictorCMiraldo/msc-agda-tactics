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

\subsection{Peano Naturals}

In terms of programing, Agda and Haskell are very close. Agda's syntax was
inspired by Haskell and, beeing also a functional language, a lot of
the programming techniques we need to use in Haskell also apply for an Agda program.
Knowledge of Haskell is not strictly necessary, but of a great value for a better
understanting of Agda.\\

The \emph{Hello World} program in Agda is to encode Peano's Natural numbers:\\[.5em]
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
data type. Pattern matching is the mechanism of choice here.\\[.5em]
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

\subsection{Propositional Logic, a fragment}

Let us continue our exposition of Agda by encoding some propositional logic. 
We first need two sets for representing the truth values:\\[.5em]
\begin{agdacode}
\begin{code}
data ⊥ : Set where

data ⊤ : Set where
  tt : ⊤
  
⊥-elim : {A : Set} → ⊥ → A
⊥-elim ()

\end{code}
\end{agdacode}


The absurd is modeled as a set with no constructors, therefore no elements. In the theory of types,
this means that there is no proof for the proposition $\bot$, as expected. Note the definition
of $\bot-elim$, it's type is, for all sets $A$\footnote{
%%%%% BEGIN FOOTNOTE
Implicit parameters are enclosed in brackets, this can be read as universal quantification in
the type level.
%%%%% END FOOTNOTE
}, $\bot \rightarrow A$. Which exactly captures
the notion of \emph{Reductio ad absurdum} in logic. It's definition is trikier, though.
Agda's empty pattern, \inlagda{()}, is used to discharge a contradiction. It tells
that there is no possible pattern in such equation, and we're discharged of writting
a right-hand side.

The top set, $\top$, on the other
hand, is written as a set with only one constructor, proving $\top$ is trivial. Yet, for reasons that will be clear 
later, we chose to encode $\top$ as a record with no fields, and therefore only one constructor, \inlagda{record\{\}} in Agda's syntax.
Following Agda's standard library notation, let's call it \AgdaType{Unit}.

\begin{agdacode}
\begin{code}
record Unit : Set where
\end{code}
\end{agdacode}

This allows us to start encoding some interesting propositional logic constructions. Let's take
conjunctions as a first candidate. We begin by declaring the set that represents conjunctions:

\begin{agdacode}
\begin{code}
data _/\_ (A B : Set) : Set where
    <_,_> : A → B → A /\ B
\end{code}
\end{agdacode}

So, \inlagda{A /\symbol{92} B} contains elements with a proof of $A$ and a proof of $B$. It's elements
can only be constructed with the \inlagda{<\_,\_>} constructor. The reader familiar with Natural Deduction
might recognize the following trivial properties:


As we shall see in chapter \ref{chap:martinlof}, these properties come for free whenever we introduce 
a new set forming operation, or, a data declaration in Agda. In fact, for each set forming operation $D$
we have four kinds of rules:
\begin{enumerate}[i)]
  \item \emph{Formation} rules for $D$ express the conditions under which $D$ is a set.
        In our example, whenever $A$ and $B$ are sets, then so is \inlagda{A /\symbol{92} B}.
  \item \emph{Introduction} rules for $D$ define the set $D$, that is, they specify how the
        cannonical elements of $D$ are constructed. For the conjunction case, 
        the elements of \inlagda{A /\symbol{92} B} have the form \inlagda{< a , b >}, where $a \in A$
        and $b \in B$. 
  \item \emph{Elimination} rules show how to prove a proposition about an arbitrary element in $D$.
        They're very closely related to structural induction. The Agda equivalent is pattern matching,
        where we deconstruct, or eliminate, an element until we find the first constructor. Note that
        the proofs of \inlagda{/\symbol{92}-elim} are simply pattern matching.
  \item \emph{Equality} rules gives us the equalities which are associated with $D$. Without diving
        too much, in our simple case, \inlagda{< a , b > == < a' , b' >} whenever \inlagda{a == a'}
        and \inlagda{b == b'}.
\end{enumerate}

An analogous technique can be employed to encode disjunction. Note the similarity with
Haskell's \inlagda{Either} datatype (they're the same, in fact). The elimination rules for
disjunction is a proof by cases. As a trivial example, we can prove that conjunction distributes
over disjunction.
  
\begin{agdacode}
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
\end{agdacode}

Using our fragment of natural deduction, we can start proving things. Let's consider a simple
proposition saying that an element of a nonempty list $l_1 ++ l_2$, where $++$ is concatenation, is
in $l_1$ or in $l_2$. For that we'll need to encode lists, provide a definition for $++$,
encode a \emph{view} of the elements in a list and finally prove our proposition.

Defining the type of lists is a boring task, and the definition is just like
it's Haskell counterpart. Let us just import the standard library and go to the
interesting part right away.

\begin{agdacode}
\begin{code}
open import Data.List using (List; _∷_; []; _++_)

data In {A : Set} : A → List A → Set where
    InHead : {xs : List A}{y : A} → In y (y ∷ xs)
    InTail : {x : A}{xs : List A}{y : A} → In y xs → In y (x ∷ xs)
\end{code}
\end{agdacode}

Now, let's look closely to this data. We have a set formin operation \inlagda{In}, that receives
one implicid parameter $A$ and is indexed by an element of $A$ and a $List A$. Indeed, \inlagda{In\; y\; l}
is the proposition that states that $x$ is an element of $l$. How do we construct such a proof?
There are two ways of doing so! Either $y$ is in $l$'s head, that's captured by the \inlagda{InHead}
constructor, or it is in $l$'s tail, and for that we require a proof of such statement, in the \inlagda{InTail}
constructor. How about the statement \inlagda{In\; y\; []}, which is clearly impossible. It is possible to see,
just from the types, that we cannot construct such statement. The result of both of \inlagda{In} constructors
are non-empty list and they are the only constructors we are allowed to use. So, the \emph{non-empty list}
requirement in the proposition we're trying to prove comes for free.

Let us see the proposition statement and it's proof step by step, as this is an interesting example.
The proposition is stated as follows,

\begin{agdacode}
\begin{code}
inDistr : {A : Set}(l₁ l₂ : List A)(x : A)
         → In x (l₁ ++ l₂) → In x l₁ \/ In x l₂
\end{code}
\end{agdacode}

The variables enclosed in normal parenthesis are called \emph{telescopes}, and they introduce
the dependent function type $(x : A) \rightarrow B\;x$, that is, $x$ can appear on the righ-hand side of
the function type constructor, $\rightarrow$. Therefore, we need an implicit set $A$, two lists of $A$,
an element of $A$ and a proof that such element is in the concatenation of the two lists.
The proof follows by \emph{induction} on the first list. 

\begin{agdacode}
\begin{code}
inDistr [] l₂ x prf = inr prf
\end{code}
\end{agdacode}

If the first list is empty, $[] ++ l_2$ reduces to $l_2$. So, prf has type \inlagda{In\; x\; l_2}, which
is just what we need to create a disjunction.

\begin{agdacode}
\begin{code}
inDistr (x ∷ l) l₂ .x InHead = inl InHead
\end{code}
\end{agdacode}

If it's not empty, though, then it has a head and a tail. Now we have to also pattern-match
on $prf$. If it says that our element is in the head of our list, the result is also very simple.
The repetition of the symbol $x$ in the left hand side is allowed as long as all duplicate occurences
are preceded by a dot. They're called dotted patterns and tell Agda that this is \emph{the only possible}
value for that pattern. We can see that by reasoning with \inlagda{InHead} type, \inlagda{In\; x\; (x :: l)}. 
So, if $l_1 = (x :: l)$ and we have $prf = In\; x\; (x :: l)$, that is, a proof that $x$ is in $l_1$'s head,
we can only be looking for $x$. 

\begin{agdacode}
\begin{code}
inDistr (x ∷ l₁) l₂ y (InTail i) 
         = \/-elim (λ a → inl (InTail a)) inr (inDistr l₁ l₂ y i)
\end{code}
\end{agdacode}

In case our element is not in $l_1$'s head, it might be either in the rest of $l_1$ or it's in $l_2$.
Note that we pass a \emph{smaller} proof to the recursive call.

%%%%% Imports for the latex compiler to work.
\ignore{
\begin{code}
open import Data.Bool using (Bool; true; false)
open import Relation.Binary.PropositionalEquality
open import Data.Product using (_×_; ∃; _,_) renaming (proj₁ to p1; proj₂ to p2)
open import Data.Sum using (_⊎_; [_,_]) renaming (inj₁ to i1; inj₂ to i2; [_,_]′ to case)
open import Function using (id; _∘_)
\end{code}
\mbox{}
}

\subsection{Relational Algebra in Agda}


\begin{TODO}
  \item This should be in another place... too complex
  \item at chapter (MartinLof) would be cool. We can actually
        use relational composition as a very nice example of
        dependent products in practice.
\end{TODO}


A very interesting exercise is to encode Relational Algebra\cite{Bird97}, where
we can truly see the advantage of dependent types in action. Most of the definitions
happens at the \emph{type level} (remember that there is no difference between types and values in Agda,
this is just a mnemonic to help understanting the \emph{functions}). The encoding presented
here is based on \cite{Jansson09}. Only high level introduction will be made in this chapter, whereas
in chapter \ref{chap:martinlof} we'll delve into more detailed explanations.

A binary relation $R$ of type $A \rightarrow B$ can be thought of in terms of several mathematical objects.
The usual definition is to say that $R \subseteq A \times B$, where $\cdot\times\cdot$ is the cartesian product of sets.
In fact, $R$ contains pairs or related elements whose first component is of type $A$ and second component is of type $B$,
note that it is slightly more general than the concept of a function, where we can have $a R b_1$ and $a R b_2$, which means
that $(a, b_1) \in R$ and $(a, b_2) \in R$, as a perfectly valid relation, but not a function, since $a$ would be mapped to two different values, $b_1$ and $b_2$.

\newcommand{\powerset}{\mathcal{P}}
Another way of speaking about relations, though, is to consider functions of type $A \rightarrow \powerset B$.
If our previous $R$ was in fact a function $f$, we would then have $f\; a = \{b_1, b_2\}$. For the more
mathematically inclined reader, the arrows $A \rightarrow \powerset B$ in the category \catname{Sets}, of sets and
functions, correspond to arrows $A \rightarrow B$ in the category \catname{Rel}, of sets and relations. For this matter,
we actually call \catname{Rel} the Kleisli Category for the monad $\powerset$. 

For our Agda encoding of Relations, we shall use a slight modification of the $\powerset$ approach.
Let's begin, in fact, by encoding set theoretic notions. The most important of all beeing undoubtly
the membership notion $\cdot \in \cdot$. One way of encoding a subset of a set $A$ is using a function
of type $A \rightarrow Bool$, the subset is obtained by $\{ a \in A | f\;a \}$. Yet, in Agda, this would
force that the deal only with decidable domains, which is not a problem if everything is finite, but
for infinite domains this would not work. More on that later.

\begin{agdacode}
\begin{code}
ℙ : Set → Set1
ℙ A = A → Set
\end{code}
\end{agdacode}





