open import Data.Bool using (Bool; true; false)
open import Relation.Binary.PropositionalEquality as PE
open import Data.Product using (Σ; _×_; ∃; _,_; uncurry′; curry) renaming (proj₁ to p1; proj₂ to p2)
open import Data.Sum using (_⊎_; [_,_]) renaming (inj₁ to i1; inj₂ to i2; [_,_]′ to case)
open import Function using (id; _∘_; _$_)
open import Data.Unit using (Unit; unit)

open import Rel.Core

module Rel.Core.Shrinking where

  -- Relational Division
  record _/_ {A B C : Set}(R : Rel B C)(S : Rel B A)(c : C)(a : A) : Set
    where 
      constructor cons-/
      field un : (b : B) → S a b → R c b

  record _\\_ {A B C : Set}(R : Rel A B)(S : Rel C B)(c : C)(a : A) : Set
    where
      constructor cons-\
      field un : (b : B) → R b a → S b c

  -- Shrinking. Emacs input is \u0
  record _↾_ {A B : Set}(R : Rel A B)(S : Rel B B)(b : B)(a : A) : Set
    where
      constructor cons-↾
      field un : (R ∩ (S / (R ᵒ))) b a

  -------------------------------
  -- Universsal

  shrink-uni-l1 : {A B : Set}(X R : Rel A B)(S : Rel B B)
                → X ⊆ (R ↾ S)
                → X ⊆ R
  shrink-uni-l1 x r s (⊆in prf) 
    = ⊆in (λ a b bXa → let bRSa = prf a b bXa
                       in p1∩ (_↾_.un bRSa))

  shrink-uni-l2 : {A B : Set}(X R : Rel A B)(S : Rel B B)
                → X ⊆ (R ↾ S)
                → (X ∙ R ᵒ) ⊆ S
  shrink-uni-l2 x r s (⊆in prf) 
    = ⊆in (λ { b b′ (a , ∙prf) 
           → let bRSa = prf a b′ (p1 ∙prf)
                 bRx→bSx = _/_.un (p2∩ (_↾_.un bRSa))
             in bRx→bSx b (p2 ∙prf) })

  shrink-uni-r : {A B : Set}(X R : Rel A B)(S : Rel B B)
               → X ⊆ R → (X ∙ R ᵒ) ⊆ S
               → X ⊆ (R ↾ S)
  shrink-uni-r x r s (⊆in xr) (⊆in xrs)
    = ⊆in (λ a b bXa 
           → let bRa = xr a b bXa
                 bXRb₁ = λ b₁ bR∘a → a , bXa , bR∘a
             in cons-↾ (cons-∩ ( bRa 
                               , cons-/ (λ b₁ bR∘a → xrs b₁ b (bXRb₁ b₁ bR∘a)))
                               )
                       )

  ------------------------
  -- Properties

  open import Rel.Core.Equality

  R≡R↾S→imgR⊆S : {A B C : Set}(R : Rel A B)(S : Rel B B)
               → R ≡r (R ↾ S) 
               → img R ⊆ S
  R≡R↾S→imgR⊆S r s (⊆in rr↾s , ⊆in r↾sr)
    = ⊆in (λ b b′ bImgRb′ 
           → let bRb′  = p1 (p2∙ bImgRb′)
                 bR∘b′ = p2 (p2∙ bImgRb′)
                 b′R↾Sa = rr↾s (p1∙ bImgRb′) b′ bRb′
             in (_/_.un $ p2∩ (_↾_.un b′R↾Sa)) b bR∘b′)

  imgR⊆S→R≡R↾S : {A B C : Set}(R : Rel A B)(S : Rel B B)
               → img R ⊆ S
               → R ≡r (R ↾ S)
  imgR⊆S→R≡R↾S r s (⊆in rs)
    = ⊆in (λ a b bRa → cons-↾ (cons-∩ 
                     ( bRa 
                     , cons-/ (λ b₁ b₁Ra → rs b₁ b (a , bRa , b₁Ra))
                     )
                   )
          )
    ,  ⊆in (λ a b bR↾Sa → p1∩ $ _↾_.un bR↾Sa)
               

  shrink-neutral : ∀{A B : Set}(R : Rel A B)
                 → R ↾ Top ≡r R
  shrink-neutral r 
    = ⊆in (λ a b bR⊤a → p1∩ $ _↾_.un bR⊤a)
    , ⊆in (λ a b bRa → cons-↾ (cons-∩ (bRa , cons-/ (λ _ _ → unit))))

  shrink-absorb : ∀{A B : Set}(R : Rel A B)
                → R ↾ Bot ≡r Bot
  shrink-absorb r
    = ⊆in (λ a b bRBota 
           → let bRa = p1∩ $ _↾_.un bRBota
             in (_/_.un $ p2∩ $ _↾_.un bRBota) b bRa)
    , ⊆in (λ a b → λ ()) 


  open import Rel.Core.Coproduct
  {-
  either-↾-distr : {A B C : Set}(R : Rel A C)(S : Rel B  C)(T : Rel C C)
                 → (either R S) ↾ T ≡r either (R ↾ T) (S ↾ T)
  either-↾-distr r s t
    = ⊆in (λ { (i1 a) c hip 
             → let cRa = either.un $ p1∩ $ _↾_.un hip
               in cons-either $ cons-↾ $ cons-∩ 
                  (cRa 
                  , cons-/ (λ c₁ h → (_/_.un $ p2∩ $ _↾_.un hip) c₁ 
                                        (cons-either h))
                  ) 
             ; (i2 b) c hip 
             → let cSb = either.un $ p1∩ $ _↾_.un hip 
               in cons-either $ cons-↾ $ cons-∩ 
                  ( cSb
                  , cons-/ (λ c₁ h → (_/_.un $ p2∩ $ _↾_.un hip) c₁
                                        (cons-either h))
                  )
             })
    , ⊆in (λ { (i1 a) c hip
             → ?
             ; (i2 a) c hip
             → {!!}
             })
    -}
