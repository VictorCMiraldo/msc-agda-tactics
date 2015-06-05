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
open import Rel.Properties.Basic
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

  private
    sup-inj : {A : Set}{x y : A}{xs : Lp (i2 x) → Lw A}{ys : Lw A}
            → sup (i2 y) (λ _ → ys) ≡ sup (i2 x) xs
            → (x ≡ y) × (xs unit ≡ ys)
    sup-inj refl = refl , refl

    sup-inj' : {A : Set}{x y : A}{xs ys : Lp (i2 x) → Lw A}
            → sup (i2 y) ys ≡ sup (i2 x) xs
            → (x ≡ y) × (xs ≡ ys)
    sup-inj' refl = refl , refl

    sup-inj-tr : {A : Set}{y : A}{xs ys : Lp (i2 y) → Lw A}
              → sup (i2 y) (λ v → xs v) ≡ sup (i2 y) (λ v → ys v)
              → sup (i2 y) (λ _ → xs unit) ≡ sup (i2 y) ys
    sup-inj-tr {y = y} refl = cong (sup (i2 y)) (fun-ext (λ { unit → refl }))
      where open import Rel.Core.HOTT using (fun-ext)

  pattern L-nil      = sup (i1 unit) _
  pattern L-cons h p = sup (i2 h) p

  inL : {A : Set} → L A (Lw A) → Lw A
  inL = +-elim (const nil) cons

  inLi1-lemma : {A : Set}{f : ⊥ → Lw A} → inL {A = A} (i1 unit) ≡ sup (i1 unit) f
  inLi1-lemma {A} {f} = cong (sup (i1 unit)) (fun-ext (λ ()))
    where open import Rel.Core.HOTT using (fun-ext)

  -- nil is unique!
  -- just a different presentation of inLi1-lemma.
  nil-unique : {A : Set}{x : Unit}{f : ⊥ → Lw A} → sup (i1 x) f ≡ nil
  nil-unique {x = unit} = cong (sup (i1 unit)) (fun-ext (λ ()))
    where
      open import Rel.Core.HOTT

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

  instance
    isEq-L : {A : Set}{{eqA : Eq A}} → Eq (Lw A)
    isEq-L {A} {{eq _≟_}} = eq iseq
      where
        open import Rel.Core.HOTT using (fun-ext) 

        iseq : (x y : Lw A) → Dec (x ≡ y)
        iseq (sup (i1 unit) f₁) (sup (i1 unit) f₂) 
          = yes (trans nil-unique (sym nil-unique))
        iseq (sup (i2 x) xs) (sup (i2 y) ys) with x ≟ y
        ...| no  x≢y = no (x≢y ∘ sym ∘ p1 ∘ sup-inj')
        ...| yes x≡y 
           rewrite x≡y
             = dec-elim 
               (λ h → yes (cong (sup (i2 y)) (fun-ext (λ { unit → h })))) 
               (λ h → no (λ j → h (p2 (sup-inj (sup-inj-tr (cong (sup (i2 y)) (p2 (sup-inj' j)))))))) 
               (iseq (xs unit) (ys unit))
        iseq (sup (i2 _) _) (sup (i1 _) _) = no (λ ())
        iseq (sup (i1 _) _) (sup (i2 _) _) = no (λ ())

    isDec-nilR : {A B : Set} → IsDec (nilR {A} {B})
    isDec-nilR {A} {B} = dec decide
      where
        decide : (x : Lw A)(y : B) → Dec (nilR x y)
        decide (sup (i1 unit) x₁) y 
          = yes ((i1 unit) , ((cons-fun (inLi1-lemma {f = x₁})) 
                , (unit , ((cons-fun refl) , unit))))
        decide (sup (i2 y) x) y₁ 
          = no (λ { (.(i1 c) , cons-fun () , (c , cons-fun refl , e)) })

    isDec-consR : {A : Set}{{eqA : Eq A}} → IsDec (consR {A})
    isDec-consR {A} {{eq _≟_}} = dec decide
      where
        open import Rel.Core.HOTT using (fun-ext)

        lemma : {x y : A}{xs : Lp (i2 x) → Lw A}{ys : Lw A}
              → x ≡ y → xs unit ≡ ys 
              → sup (i2 y) (λ _ → ys) ≡ sup (i2 x) xs
        lemma {x = x} refl refl = cong (sup (i2 x)) (fun-ext (λ { unit → refl }))

        decide : (x : Lw A)(y : A × Lw A) → Dec (consR x y)
        decide (sup (i1 unit) f) (y , ys) 
          = no (λ { (.(i2 (y , ys)) , cons-fun () , cons-fun refl) })
        decide (sup (i2 x)   xs) (y , ys) 
          with x ≟ y | Eq.cmp (isEq-L {{eq _≟_}}) (xs unit) ys 
        ...| yes x≡y | yes xs≡ys 
           = yes (i2 (y , ys) , (cons-fun (lemma x≡y xs≡ys)) , (cons-fun refl))
        ...| yes x≡y | no  xs≢ys 
           = no (λ { (.(i2 (y , ys)) , (cons-fun d , cons-fun refl)) 
                   → xs≢ys (p2 (sup-inj d)) })
        ...| no  x≢y | yes xs≡ys
           = no (λ { (.(i2 (y , ys)) , (cons-fun d , cons-fun refl)) 
                   → x≢y (p1 (sup-inj d)) })
        ...| no  x≢y | no  xs≢ys
           = no (λ { (.(i2 (y , ys)) , (cons-fun d , cons-fun refl)) 
                   → xs≢ys (p2 (sup-inj d)) })

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
              ≡r⟨ (tactic (by (quote +-bi-functor))) ⟩ 
                 ((Id ∙ Id) + (Id * R ∙ Id * S)) ∙ ι₁
              ≡r⟨ (tactic (by (quote ι₁-natural))) ⟩ 
                 ι₁ ∙ (Id ∙ Id)
              ≡r⟨ (tactic (by (quote ∙-id-r))) ⟩
                 ι₁ ∙ Id
              ∎ 

            aux2 : (Id + (Id * R) ∙ Id + (Id * S)) ∙ ι₂ ≡r ι₂ ∙ Id * (R ∙ S)
            aux2 = begin 
                 (Id + (Id * R) ∙ Id + (Id * S)) ∙ ι₂
              ≡r⟨ (tactic (by (quote +-bi-functor))) ⟩
                 (Id ∙ Id) + (Id * R ∙ Id * S) ∙ ι₂
              ≡r⟨ (tactic (by (quote ι₂-natural))) ⟩ 
                 ι₂ ∙ Id * R ∙ Id * S
              ≡r⟨ (tactic (by (quote *-bi-functor))) ⟩
                 ι₂ ∙ (Id ∙ Id) * (R ∙ S)
              ≡r⟨ (tactic (by (quote ∙-id-r))) ⟩
                 ι₂ ∙ Id * (R ∙ S)
              ∎ 

        postulate 
          a : {A : Set} → A
        fromJust : {A : Set} → Maybe A → A
        fromJust (just x) = x
        fromJust nothing  = a

        open import RW.Language.RTermUtils
        open import RW.Language.Instantiation

        lemma-ᵒ : {I A B : Set} {R : Rel A B}
                → Id {Unit} + (Id {I} * (R ᵒ)) ≡r (Id + (Id * R)) ᵒ
        lemma-ᵒ {R = R} = begin 
                Id + (Id * (R ᵒ))
              ≡r⟨ (tactic (by (quote idmp-id-ᵒ))) ⟩
                (Id ᵒ) + (Id * (R ᵒ))
              ≡r⟨ (tactic (by (quote idmp-id-ᵒ))) ⟩
                (Id ᵒ) + ((Id ᵒ) * (R ᵒ))
              ≡r⟨ (tactic (by (quote *-ᵒ-distr))) ⟩ 
                (Id ᵒ) + ((Id * R) ᵒ)
              ≡r⟨ (tactic (by (quote +-ᵒ-distr))) ⟩
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
