open import Prelude hiding (_*_; _+_; _++_) renaming (either to +-elim)

open import Rel.Core
open import Rel.Core.Equality
open import Rel.Core.Product
open import Rel.Core.Coproduct
open import Rel.Core.Correflexive
open import Rel.Relator

open import Rel.Properties.BiFunctor
open import Rel.Properties.Basic
open import Rel.Properties.Idempotence
open import Rel.Core.Helper.Injections

open import Rel.Relator.List

open import Rel.Reasoning.RelationJudgement  
open import Rel.Reasoning.RelEq-Strategy
open import RW.RW (rel-≡r-strat ∷ [])

module Rel.Relator.List.Defs where

  ------------------------
  -- Definitions over L --
  ------------------------

  open IsWFunctor1 {{...}}
  open IsRelator   {{...}}

  -- nil is unique!
  -- just a different presentation of inLi1-lemma.
  nil-unique : {A : Set}{x : Unit}{f : ⊥ → Lw A} → sup (i1 x) f ≡ nil
  nil-unique {x = unit} = cong (sup (i1 unit)) (fun-ext (λ ()))
    where
      open import Rel.Core.HOTT


  -- List concatenation
  _++_ : {A : Set} → Lw A → Lw A → Lw A
  (sup (i1 _) _) ++ l2 = l2
  (sup (i2 s) p) ++ l2 = sup (i2 s) (λ ss → p ss ++ l2)

  ++-nil-nil : {A : Set}{l1 l2 : Lw A} → l1 ++ l2 ≡ nil → l1 ≡ nil × l2 ≡ nil
  ++-nil-nil {l1 = sup (i1 unit) f} {sup (i1 .unit) .(λ ())} refl = nil-unique , refl
  ++-nil-nil {l1 = sup (i1 x) x₁} {sup (i2 y) x₂} ()
  ++-nil-nil {l1 = sup (i2 y) x} ()

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

  add-non-empty : {A : Set}(a : A)(l : Lw A) → add nil (a , l) → ⊥
  add-non-empty a l ((w1 , w2) , (cons-fun un , proj₂)) with ++-nil-nil {l1 = w1} {l2 = w2} un
  add-non-empty a l ((w1 , .(sup (i1 unit) (λ ()))) , (cons-fun un , (.w1 , .k) 
                    , (cons-⟨,⟩ ((.w1 , cons-fun refl , cons-fun refl) 
                    , (k , (.(i2 k) , cons-fun () , cons-fun refl) , cons-fun refl)) , c2))) | _ , refl 

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
  permcons-lemma = ?
  {-
  TODO: why is this proof taking so long to typecheck?

  permcons-lemma = begin
        perm ∙ fun inL ∙ ι₂
      ≡r⟨ (tactic (by (quote ∙-assoc))) ⟩
        (perm ∙ fun inL) ∙ ι₂
      ≡r⟨ ≡r-cong (λ z → z ∙ ι₂) cata-cancel ⟩
         ((either nilR add) ∙ (Id + (Id * perm))) ∙ ι₂
      ≡r⟨ (tactic (by (quote ∙-assoc))) ⟩
         (either nilR add) ∙ (Id + (Id * perm)) ∙ ι₂
      -- ≡r⟨ ≡r-cong (λ z → (either nilR add) ∙ z) (≡r-sym ι₂-natural) ⟩
      ≡r⟨ (tactic (by (quote ι₂-natural))) ⟩
         (either nilR add) ∙ ι₂ ∙ Id * perm
      ≡r⟨ (tactic (by (quote ∙-assoc))) ⟩
        ((either nilR add) ∙ ι₂) ∙ Id * perm
      ≡r⟨ (tactic (by (quote ι₂-cancel))) ⟩
      -- ≡r⟨ ≡r-cong (λ z → z ∙ Id * perm) ι₂-cancel ⟩
         add ∙ Id * perm
      ∎
    where       
      open ≡r-Reasoning
  -}

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
              (≡r-trans (≡r-cong (λ z → z ∙ Id * perm) add≡permcons) ∙-assocᵢ)

  perm-elem : {A : Set}{{_ : Eq A}}
            → perm {A = A} ∙ elem ≡r elem
  perm-elem {A} {{eq f}} = TODO -- ⊆in aux1 , ⊆in {!!}
    where
      postulate TODO : ∀{α}{A : Set α} → A
      {-
        stack overflowing... :(
      aux1 : (a : A)(b : Lw A) → (perm ∙ elem {{eq f}}) b a → elem {{eq f}} b a
      aux1 a (sup (i1 x) x₁) (sup (i1 x₂) x₃ , (cons-cata c1 , ()))
      aux1 a (sup (i1 x) x₁) (sup (i2 y) x₂ , (cons-cata (.(i2 (y , k2)) , cons-either c , cons-either ((.y , k2) 
                             , cons-fun refl , cons-⟨,⟩ ((.y , cons-fun refl , cons-fun refl) , d2))) , c2)) 
        = add-non-empty y k2 (subst (λ z → add z (y , k2)) nil-unique c)
      aux1 a (sup (i2 y) x) hip with f y a
      ...| yes prf = unit
      aux1 a (sup (i2 y) x) (sup (i1 x₁) x₂ , (cons-cata un , ())) | no prf
      aux1 a (sup (i2 y) x) (sup (i2 j) x₂ , (cons-cata (.(i2 (j , k2)) , cons-either c , cons-either ((.j , k2) 
                             , cons-fun refl , cons-⟨,⟩ ((.j , cons-fun refl , cons-fun refl) , d2))) , c2)) 
           | no prf = aux1 a (x unit) {!!}
      -- aux1 a (sup (i2 y) x) (sup (i2 y₁) x₁ , (cons-cata (.(i2 k2) , cons-either c1 , cons-either (k2 , (cons-fun refl , c22))) , proj₂)) 
      --   | no prf = aux1 y {!!} {!!}
      -}
