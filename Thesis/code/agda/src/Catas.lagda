\begin{code}
open import Prelude
open import Rel.Core
open import Rel.Core.Equality
\end{code}

%<*wtype-def>
\begin{code}
data W (S : Set)(P : S → Set) : Set where
  sup : (s : S) → (P s → W S P) → W S P
\end{code}
%</wtype-def>

%<*wfunctor>
\begin{code}
record IsWFunctor1 (F : Set → Set → Set) : Set1 where
  field
    S : Set → Set
    P : {A : Set} → S A → Set
    
    inF  : {A : Set} → F A (W (S A) P) → W (S A) P
    outF : {A : Set} → W (S A) P → F A (W (S A) P)

    Fᵣ : {X A B : Set} → Rel A B → Rel (F X A) (F X B)

  μF : Set → Set
  μF A = W (S A) P 

  inR : {A : Set} → Rel (F A (μF A)) (μF A)
  inR = fun inF

  outR : {A : Set} → Rel (μF A) (F A (μF A))
  outR = fun outF
\end{code}
%</wfunctor>

\begin{code}
open IsWFunctor1 {{...}}

μ : (F : Set → Set → Set){{ _ : IsWFunctor1 F }}
   → Set → Set
μ F A = μF {F = F} A
\end{code}

\begin{code}
{-# TERMINATING #-}
\end{code}
%<*w-elim>
\begin{code}
W-rec : ∀{c}{S : Set}{P : S → Set}
     → {C : W S P → Set c}
     → (c : (s : S)  
          → (f : P s → W S P) 
          → (h : (p : P s) → C (f p)) 
          → C (sup s f)) 
     → (x : W S P) → C x 
W-rec {C = C} c (sup s f) = c s f (W-rec {C = C} c ∘ f)
\end{code}
%</w-elim>

\begin{code}
{-# TERMINATING #-}
\end{code}
%<*w-elim-rel>
\begin{code}
W-rec-rel : {S : Set}{P : S → Set}{A : Set}
          → ((s : S) → (p : P s → W S P) → Rel (W S P) A → A → Set)
          → Rel (W S P) A
W-rec-rel h a w = W-rec (λ s p c → h s p (W-rec-rel h) a) w
\end{code}
%</w-elim-rel>

%<*w-cata>
\begin{code}
W-cata-F : {A B : Set}{F : Set → Set → Set}{{ prf : IsWFunctor1 F }}
           (R : Rel (F A B) B) → Rel (μF A) B
W-cata-F {A} {B} {F} R = W-rec-rel (λ s p h n → gene h n (sup s p))
  where
    gene : Rel (μF A) B → Rel (μF A) B
    gene h n l = (R ∙ Fᵣ h) n (outF l)
\end{code}
%</w-cata>

%<*relator>
\begin{code}
record IsRelator (F : Set → Set → Set) {{ p : IsWFunctor1 F }} 
     : Set1 where 
  field
    fmap-id : ∀{B A} → (Fᵣ Id) ≡r Id

    fmap-∙ : ∀{I A B C}{R : Rel B C}{S : Rel A B}
           → Fᵣ (R ∙ S) ≡r Fᵣ R ∙ Fᵣ S

    fmap-ᵒ : ∀{I A B}{R : Rel A B}
           → Fᵣ (R ᵒ) ≡r (Fᵣ R) ᵒ

    fmap-⊆ : ∀{I A B}{R S : Rel A B}
           → R ⊆ S → Fᵣ R ⊆ Fᵣ S
\end{code}
%</relator>

%<*cata>
\begin{code}
record ⟦_⟧₁ {A B : Set}{F : Set → Set → Set}{{ prf : IsWFunctor1 F }}
            (R : Rel (F A B) B)(b : B)(μFa : μF A) : Set
  where constructor cons-cata
        field un : W-cata-F R b μFa
\end{code}
%</cata>

%<*cata-uni>
\begin{code}
postulate
  cata-uni-1 : {A B : Set}{F : Set → Set → Set}
               {{ pF : IsWFunctor1 F }}{{ pR : IsRelator F }}
               {R : Rel (F A B) B}{X : Rel (μF A) B}
             → X ⊆ R ∙ Fᵣ X ∙ outR
             → X ⊆ ⟦ R ⟧₁

  cata-uni-2 : {A B : Set}{F : Set → Set → Set}
               {{ pF : IsWFunctor1 F }}{{ pR : IsRelator F }}
               {R : Rel (F A B) B}{X : Rel (μF A) B}
             → R ∙ Fᵣ X ∙ outR ⊆ X
             → ⟦ R ⟧₁ ⊆ X
\end{code}
%</cata-uni>
