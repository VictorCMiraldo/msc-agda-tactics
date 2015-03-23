open import Prelude hiding (_*_; _+_; _++_) renaming (either to +-elim)

open import Rel.Core
open import Rel.Core.Equality
open import Rel.Core.Product
open import Rel.Core.Coproduct
open import Rel.Relator

open import Rel.Reasoning.RelEq-Strategy
open import RW.RW (rel-≡r-strat ∷ [])
open import RW.Language.RTerm
open import RW.Language.RTermUtils

open import Rel.Properties.BiFunctor
open import Rel.Properties.Neutral
open import Rel.Properties.Basic hiding (∙-id-r)
open import Rel.Properties.Idempotence
open import Rel.Core.Helper.Injections
open import Rel.Reasoning.RelationJudgement         
open ≡r-Reasoning

module Rel.Relator.List where

  -- A List encoded as a W-type
  L : Set → Set → Set
  L A X = Unit ⊎ (A × X)

  Ls : Set → Set
  Ls = _⊎_ Unit

  Lp : {A : Set} → Ls A → Set
  Lp = +-elim (const ⊥) (const Unit)

  Lw : Set → Set
  Lw A = W (Ls A) Lp

  nil : {A : Set} → Lw A
  nil = sup (i1 unit) (λ ())

  cons : {A : Set} → A × Lw A → Lw A
  cons (h , t) = sup (i2 h) (const t)

  pattern L-nil      = sup (i1 unit) _
  pattern L-cons h p = sup (i2 h) p

  inL : {A : Set} → L A (Lw A) → Lw A
  inL = +-elim (const nil) cons

  inLi1-lemma : {A : Set}{f : ⊥ → Lw A} → inL {A = A} (i1 unit) ≡ sup (i1 unit) f
  inLi1-lemma {A} {f} = cong (sup (i1 unit)) (fun-ext (λ ()))
    where open import Rel.Core.HOTT using (fun-ext)

  inLi2-lemma : {A : Set}{a : A}{f : Lp (i2 a) → Lw A}
              → inL (i2 (a , f unit)) ≡ sup (i2 a) f
  inLi2-lemma {a = a} = cong (sup (i2 a)) (fun-ext (λ { unit → refl }))
    where open import Rel.Core.HOTT using (fun-ext)

  outL : {A : Set} → Lw A → L A (Lw A)
  outL (sup (i1 x) x₁) = i1 unit
  outL (sup (i2 y) x) = i2 (y , x unit)

  nilR : {A B : Set} → Rel B (Lw A)
  nilR = fun inL ∙ ι₁ ∙ Top

  consR : {A : Set} → Rel (A × Lw A) (Lw A)
  consR = fun inL ∙ ι₂

  open IsWFunctor1 {{...}}
  open IsRelator {{...}}

  instance
    IsWFunctor1-L : IsWFunctor1 L
    IsWFunctor1-L = record
      { S = Ls
      ; P = Lp
      ; inF = inL
      ; outF = outL
      ; Fᵣ = λ R → Id + (Id * R)
      }
    
    IsRelator-L : IsRelator L
    IsRelator-L = record
      { fmap-id = lemma-id
      ; fmap-∙  = lemma-∙
      ; fmap-ᵒ  = lemma-ᵒ
      ; fmap-⊆  = lemma-⊆
      } where
          
        lemma-id : {A B C : Set} → Id + (Id * Id) ≡r Id {A ⊎ (B × C)}
        lemma-id {A} {B} {C}
          = subst (λ x → Id {A} + x ≡r Id) (≡r-promote (≡r-sym *-id)) +-id

        lemma-∙ : {I : Set}{A B C : Set} {R : Rel B C} {S : Rel A B}
                → Id {Unit} + (Id {I} * (R ∙ S)) ≡r Id + (Id * R) ∙ Id + (Id * S)
        lemma-∙ {I} {A} {B} {C} {R} {S} 
          = ≡r-sym (coprod-uni-l (ι₁ ∙ Id) (ι₂ ∙ Id * (R ∙ S)) 
                                 (≡r-sym aux1) (≡r-sym aux2))
          where
            aux1 : (Id + (Id * R) ∙ Id + (Id * S)) ∙ ι₁ ≡r ι₁ ∙ Id
            aux1 = begin 
                 (Id + (Id * R) ∙ Id + (Id * S)) ∙ ι₁
              ≡r⟨ ≡r-cong (λ s → s ∙ ι₁) +-bi-functor ⟩ 
                 ((Id ∙ Id) + (Id * R ∙ Id * S)) ∙ ι₁
              ≡r⟨ ≡r-sym ι₁-natural ⟩ 
                 ι₁ ∙ (Id ∙ Id)
              ≡r⟨ ≡r-cong (_∙_ ι₁) (≡r-sym (∙-id-r Id)) ⟩
                 ι₁ ∙ Id
              ∎ 

            aux2 : (Id + (Id * R) ∙ Id + (Id * S)) ∙ ι₂ ≡r ι₂ ∙ Id * (R ∙ S)
            aux2 = begin 
                 (Id + (Id * R) ∙ Id + (Id * S)) ∙ ι₂
              ≡r⟨ (tactic (by (quote +-bi-functor))) ⟩
                 (Id ∙ Id) + (Id * R ∙ Id * S) ∙ ι₂
              ≡r⟨ ≡r-sym ι₂-natural ⟩ 
                 ι₂ ∙ Id * R ∙ Id * S
              ≡r⟨ ≡r-cong (_∙_ ι₂) *-bi-functor ⟩
                 ι₂ ∙ (Id ∙ Id) * (R ∙ S)
              ≡r⟨ (tactic (by (quote ∙-id-r))) ⟩
                 ι₂ ∙ Id * (R ∙ S)
              ∎ 

        lemma-ᵒ : {I A B : Set} {R : Rel A B}
                → Id {Unit} + (Id {I} * (R ᵒ)) ≡r (Id + (Id * R)) ᵒ
        lemma-ᵒ {R = R} = begin 
                Id + (Id * (R ᵒ))
              ≡r⟨ ≡r-cong (λ i → i + (Id * (R ᵒ))) idmp-id-ᵒ ⟩
                (Id ᵒ) + (Id * (R ᵒ))
              ≡r⟨ ≡r-cong (λ i → (Id ᵒ) + (i * (R ᵒ))) idmp-id-ᵒ ⟩
                (Id ᵒ) + ((Id ᵒ) * (R ᵒ))
              ≡r⟨ ≡r-cong (λ i → (Id ᵒ) + i) *-ᵒ-distr ⟩
                (Id ᵒ) + ((Id * R) ᵒ)
              ≡r⟨ +-ᵒ-distr ⟩
                (Id + (Id * R)) ᵒ
              ∎

        lemma-⊆ : {I J A B : Set} {R : Rel A B} {S : Rel A B}
                → R ⊆ S → Id {I} + (Id {J} * R) ⊆ Id + (Id * S)
        lemma-⊆ {R = R} (⊆in rs) 
          = ⊆in (λ { (i1 a) (i1 b) (cons-either (h , cons-fun i1b≡h , cons-fun h≡a)) 
                     → cons-either (b , cons-fun refl , cons-fun (trans h≡a (i1-inj i1b≡h)))
                   ; (i1 _) (i2 _) (cons-either (_ , cons-fun () , _))
                   ; (i2 _) (i1 _) (cons-either (_ , cons-fun () , _))
                   ; (i2 a) (i2 b) (cons-either (h , cons-fun b≡h , cons-⟨,⟩ ((x11 , x12) , (x21 , x22))))
                     → cons-either (b , (cons-fun refl 
                       , cons-⟨,⟩ (((p1 h) , (cons-fun (cong p1 (i2-inj b≡h)) , cons-fun (trans (fun.un (p2 x12)) (fun.un (p1 x12))))) 
                       , x21 , rs x21 (p2 b) (subst (λ i → R (p2 i) x21) (i2-inj b≡h) (p1 x22)) , (p2 x22))))
                   })

  ------------------------
  -- Definitions over L --
  ------------------------

  -- Here we'll provide a few definitions from the AoP book, together with a few results
  -- that might help one to start calculating faster, instead of proving standard results.

  -- TODO: this is horrible...
  -- This provides a structured way to construct an element of a cata of a list.
  cataL-prf : {A B : Set}{N : Rel Unit B}{C : Rel (A × B) B}
              {b : B}(la : L A (Lw A))
            → +-elim (N b) (λ l' → ∃ (λ b' → ⟦ either N C ⟧₁ b' (p2 l') × C b (p1 l' , b'))) la
            → ⟦ either N C ⟧₁ b (inF la)
  cataL-prf (i1 unit) hip 
            = cons-cata ((i1 unit) , ((cons-either hip) , (cons-either (unit , ((cons-fun refl) , cons-fun refl)))))
  cataL-prf (i2 y) (b' , IH , r) 
            = cons-cata ((i2 (p1 y , b')) , ((cons-either r) , (cons-either ((p1 y , b') 
            , (cons-fun refl) , (cons-⟨,⟩ (((p1 y) , ((cons-fun refl) , (cons-fun refl))) 
            , ((p2 y) , (⟦_⟧₁.un IH , (cons-fun refl)))))))))

  -- List concatenation
  _++_ : {A : Set} → Lw A → Lw A → Lw A
  (sup (i1 _) _) ++ l2 = l2
  (sup (i2 s) p) ++ l2 = sup (i2 s) (λ ss → p ss ++ l2)

  cat : {A : Set} → Rel (Lw A × Lw A) (Lw A)
  cat = fun (uncurry _++_)

  -- Membership relation
  elem : {A : Set}{{ eqA : Eq A }} → Rel A (Lw A)
  elem {{ eq f }} (sup (i1 _) _) _ = ⊥
  elem {{ eq f }} (sup (i2 y) p) a with f y a
  ...| yes _ = Unit
  ...| no  _ = elem {{ eq f }} (p unit) a

  -- simple iso.
  exch : {X Y Z : Set} → Rel (X × (Y × Z)) (Y × (X × Z))
  exch = fun (λ xyz → p1 (p2 xyz) , (p1 xyz , p2 (p2 xyz)) )

  -- ⊢ (x ++ [z] ++ y) add (z , x ++ y)
  add : {A : Set} → Rel (A × Lw A) (Lw A)
  add = cat ∙ (Id * consR) ∙ exch ∙ (Id * cat ᵒ)

  -- Permutations, as defined in the AoP book.
  perm : {A : Set} → Rel (Lw A) (Lw A)
  perm = ⟦ either nilR add ⟧₁

  -- Permutations are reflexive.
  perm-refl : {A : Set} → Id ⊆ perm {A = A}
  perm-refl {A} = cata-uni-1 (⊆in aux)
    where
      aux : (a b : Lw A) → Id b a → ((either nilR add) ∙ (Id + (Id * Id)) ∙ outR) b a
      aux (sup (i1 unit) f) .(sup (i1 unit) f) (cons-fun refl) 
        = i1 unit , (cons-either ((i1 unit) , (cons-fun (inLi1-lemma {f = f}) , unit , (cons-fun refl , unit))) 
                  , ((i1 unit) , (cons-either (unit , ((cons-fun refl) , (cons-fun refl))) , (cons-fun refl))))
      aux (sup (i2 y) x) .(sup (i2 y) x) (cons-fun refl) 
        = i2 (y , x unit) , (cons-either ((nil , sup (i2 y) x) , (cons-fun refl , ((nil , y , x unit) 
                          , ((cons-⟨,⟩ ((nil , ((cons-fun refl) , (cons-fun refl))) 
                                               , ((y , x unit) , ((i2 (y , x unit) , ((cons-fun inLi2-lemma) , (cons-fun refl))) , (cons-fun refl))))) 
                                               , ((y , nil , x unit) , ((cons-fun refl) , (cons-⟨,⟩ ((y , ((cons-fun refl) , (cons-fun refl))) 
                                               , (x unit , ((cons-ᵒ (cons-fun refl)) , (cons-fun refl))))))))))) 
        , ((i2 (y , x unit)) , ((cons-either ((y , x unit) , ((cons-fun refl) 
        , (cons-⟨,⟩ ((y , ((cons-fun refl) , (cons-fun refl))) , ((x unit) , ((cons-fun refl) , (cons-fun refl)))))
          ))) 
        , (cons-fun refl))))

  -- Simple lemma to rewrite perm.
  permcons-lemma : {A : Set} → perm {A = A} ∙ consR ≡r add ∙ (Id * perm)
  permcons-lemma = begin
        perm ∙ fun inL ∙ ι₂
      ≡r⟨ ≡r-sym ∙-assoc ⟩
        (perm ∙ fun inL) ∙ ι₂
      ≡r⟨ ≡r-cong (λ z → z ∙ ι₂) cata-cancel ⟩
         ((either nilR add) ∙ (Id + (Id * perm))) ∙ ι₂
      ≡r⟨ ∙-assoc ⟩
         (either nilR add) ∙ (Id + (Id * perm)) ∙ ι₂
      ≡r⟨ ≡r-cong (λ z → (either nilR add) ∙ z) (≡r-sym ι₂-natural) ⟩
         (either nilR add) ∙ ι₂ ∙ Id * perm
      ≡r⟨ ≡r-sym ∙-assoc ⟩
        ((either nilR add) ∙ ι₂) ∙ Id * perm
      ≡r⟨ ≡r-cong (λ z → z ∙ Id * perm) ι₂-cancel ⟩
         add ∙ Id * perm
      ∎
    where
      open import Rel.Reasoning.RelationJudgement         
      open ≡r-Reasoning

  -- Now, we can also rewrite add in tems of perm.
  -- TODO: remove that ugly postulate... how?
  add≡permcons : {A : Set} → add {A = A} ≡r perm ∙ consR
  add≡permcons {A} = ≡r-trans (⊆in aux1 , ⊆in aux2) (≡r-sym permcons-lemma)
    where
      aux1 : (a : A × Lw A)(b : Lw A) → add b a → (add ∙ Id * perm) b a
      aux1 (a , la) b hip 
        = (a , la) , hip , cons-⟨,⟩ ((a , (cons-fun refl , cons-fun refl)) , la 
                                    , ((⊆out perm-refl la la (cons-fun refl)) , (cons-fun refl)))

      aux2 : (a : A × Lw A)(b : Lw A) → (add ∙ Id * perm) b a → add b a
      aux2 (.m2 , la) .(m1 ++ (sup (i2 m2) (const m3))) ((.m2 , .(m1 ++ m3)) 
                      , ((.m1 , .(sup (i2 m2) (const m3))) , (cons-fun refl , ((m1 , m2 , m3) 
                      , cons-⟨,⟩ ((.m1 , cons-fun refl , cons-fun refl) , (.(m2 , m3) , (._ , cons-fun refl , cons-fun refl) , cons-fun refl)) 
                      , (.m2 , .m1 , .m3) , cons-fun refl 
                      , cons-⟨,⟩ ((.m2 , cons-fun refl , cons-fun refl) , (.(m1 ++ m3) , cons-ᵒ (cons-fun refl) , cons-fun refl))))) 
                      , cons-⟨,⟩ ((.m2 , cons-fun refl , cons-fun refl) , (.la , p1 , cons-fun refl))) 
           = (m1 , sup (i2 m2) (const m3)) 
           , ((cons-fun refl) , ((m1 , m2 , m3) 
           , ((cons-⟨,⟩ ((m1 , ((cons-fun refl) , (cons-fun refl))) , ((m2 , m3) , ((i2 (m2 , m3) , ((cons-fun refl) , (cons-fun refl))) , (cons-fun refl))))) 
           , ((m2 , m1 , m3) , ((cons-fun refl) , (cons-⟨,⟩ ((m2 , (cons-fun refl) , (cons-fun refl)) 
           , (m1 ++ m3 , ((cons-ᵒ (cons-fun refl)) , (cons-fun ok))))))))))
           where postulate ok : la ≡ m1 ++ m3

               
  permRec : {A : Set} 
          → perm {A = A} ≡r ⟦ either nilR (perm ∙ consR) ⟧₁
  permRec = ≡r-cong (λ z → ⟦ either nilR z ⟧₁) add≡permcons

  permLemma : {A : Set} 
            → perm {A = A} ∙ consR ≡r perm ∙ consR ∙ (Id * perm)
  permLemma = ≡r-trans permcons-lemma 
              (≡r-trans (≡r-cong (λ z → z ∙ Id * perm) add≡permcons) ∙-assoc)

      
  {-
  module Example where

    l1 : Lw ℕ
    l1 = cons (1 , nil)

    l2 : Lw ℕ
    l2 = cons (1 , cons (2 , nil))

    prefix : Rel (Lw ℕ) (Lw ℕ)
    prefix = ⟦ either nilR (nilR ∪ consR) ⟧₁

    {-# TERMINATING #-}
    prf : prefix l1 l2
    prf = cons-cata 
        ( i2 (1 , nil) 
        , (cons-either (cons-∪ (i2 (i2 (1 , nil) , (cons-fun refl) , (cons-fun refl)))) 
            , (cons-either ((1 , nil) 
              , (cons-fun refl , 
                (cons-⟨,⟩ ((1 , ((cons-fun refl) , (cons-fun refl))) 
                , cons (2 , nil) , (((i2 (2 , nil)) , 
                                   ((cons-either (cons-∪ (i1 (i1 unit , cons-fun refl , unit , cons-fun refl , unit)))) 
                                   , (cons-either ((2 , nil) , (cons-fun refl , cons-⟨,⟩ ((2 , ((cons-fun refl) , (cons-fun refl))) 
                                     , nil , (((i1 unit) , ((cons-either (i1 unit , cons-fun refl , unit , cons-fun refl , unit)) 
                                     , (cons-either (unit , cons-fun refl , cons-fun refl)))) , cons-fun refl)))))
        )) , cons-fun refl))))))))
  -}
