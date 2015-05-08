open import Rel.Core
open import Rel.Core.Equality
open import Rel.Core.Product
open import Rel.Core.Coproduct
open import Rel.Core.Helper.Injections

-- Keeps the bifunctor properties of product and coproduct in rel
-- together.
module Rel.Properties.BiFunctor where

  -----------------
  -- * Product * --
  -----------------

  -- Unfortunately, for products, we don't have an equality for
  -- π₁ and π₂ natural-like properties. To see why, take
  -- S = Bot and convert to pointwise.
  --
  -- 1) b (R ∙ π₁) (a , _) ⇒ b R a
  --
  -- 2) b (π₁ ∙ (R * S)) (a , c) 
  --      ⇒ ∃ (a', c') . b = a' ∧ a' R a ∧ c' Bot c
  --      ⇒ ∃ (a', c') . b = a' ∧ a' R a ∧ False
  --
  -- Even though (1) guarantees the existance of a pair (b , a) ∈ R,
  -- it doesn't imply (2), which is trivially the false propositon.
  --
  -- Yet, we still have inclusion!
  --

  π₁-natural : {A B C D : Set}{R : Rel A B}{S : Rel C D}
              → π₁ ∙ (R * S) ⊆ R ∙ π₁
  π₁-natural {R = R} {S = S} 
    = prod-uni-r1 (R ∙ π₁) (S ∙ π₂) ⊆-refl

  π₂-natural : {A B C D : Set}{R : Rel A B}{S : Rel C D}
             → π₂ ∙ (R * S) ⊆ S ∙ π₂
  π₂-natural {R = R} {S = S} 
    = prod-uni-r2 (R ∙ π₁) (S ∙ π₂) ⊆-refl

  *-bi-functor : {A B C X Y Z : Set}
                 { R : Rel B C }{H : Rel A B }
                 { S : Rel Y Z }{I : Rel X Y } 
               → (R * S) ∙ (H * I) ≡r (R ∙ H) * (S ∙ I)
  *-bi-functor {A} {B} {C} {X} {Y} {Z} {R} {H} {S} {I} 
    = ⊆in aux1 , ⊆in aux2
    where
      aux1 : (a : A × X) (b : C × Z) → (R * S ∙ H * I) b a → ((R ∙ H) * (S ∙ I)) b a
      aux1 (a , x) (c , z) ((w1 , w2) , (cons-⟨,⟩ (p11 , p12) , cons-⟨,⟩ (p21 , p22))) 
        = cons-⟨,⟩ ((a , ((w1 , (fun-kill-1 p11 , fun-kill-1 p21)) , (cons-fun refl))) 
                   , x , ((w2 , (fun-kill-1 p12 , fun-kill-1 p22)) , (cons-fun refl)))

      aux2 : (a : A × X) (b : C × Z) → ((R ∙ H) * (S ∙ I)) b a → (R * S ∙ H * I) b a
      aux2 (a , x) (c , z) (cons-⟨,⟩ ((wh1 , ph11 , ph12) , (wh2 , ph21 , ph22))) 
        = (p1∙ ph11 , p1∙ ph21) 
        , cons-⟨,⟩ (((p1∙ ph11) , ((p1 $ p2∙ ph11) , (cons-fun refl))) , ((p1∙ ph21) , ((p1 $ p2∙ ph21) , (cons-fun refl))))
        , cons-⟨,⟩ ((wh1 , (p2 $ p2∙ ph11) , ph12) , (wh2 , (p2 $ p2∙ ph21) , ph22))

  *-ᵒ-distr : {A B C D : Set}{R : Rel A B}{S : Rel C D}
            → (R ᵒ * S ᵒ) ≡r (R * S) ᵒ
  *-ᵒ-distr {R = R} {S = S} 
    = ⊆in (λ { (b , d) (a , c) (cons-⟨,⟩ ((hb , cons-ᵒ h1 , cons-fun f) , (hd , cons-ᵒ h2 , cons-fun g))) 
           → cons-ᵒ $ cons-⟨,⟩ ((a , subst (λ x → R x a) (sym f) h1 , cons-fun refl) , (c , subst (λ x → S x c) (sym g) h2 , cons-fun refl)) })
    , ⊆in (λ { (b , d) (a , c) (cons-ᵒ (cons-⟨,⟩ ((ha , h1 , cons-fun f) , (hc , h2 , cons-fun g)))) 
           → cons-⟨,⟩ ((b , cons-ᵒ (subst (R b) (sym f) h1) , cons-fun refl) , (d , cons-ᵒ (subst (S d) (sym g) h2) , cons-fun refl)) })

  *-id : {A B : Set} → Id * Id ≡r Id {A × B}
  *-id {A} {B} = ⊆in aux1 , ⊆in aux2
    where
      aux1 : (a b : A × B) → (Id * Id) b a → Id b a
      aux1 a b (cons-⟨,⟩ ((w1 , c11 , c12) , (w2 , c21 , c22))) 
        rewrite sym (fun.un c11)
              | sym (fun.un c21)
              | sym (fun.un c12)
              | sym (fun.un c22)
              = cons-fun (cong₂ _,_ (fun.un c11) (fun.un c21))

      aux2 : (a b : A × B) → Id b a → (Id * Id) b a
      aux2 a b (cons-fun a≡b) rewrite a≡b 
        = cons-⟨,⟩ ( (p1 b , cons-fun refl , cons-fun refl) 
                   , p2 b , cons-fun refl , cons-fun refl)

  -------------------
  -- * Coproduct * --
  -------------------

  ι₁-natural : {A B C D : Set}{R : Rel A B}{S : Rel C D}
             → ι₁ ∙ R ≡r (R + S) ∙ ι₁
  ι₁-natural {R = R} {S = S}
    = coprod-uni-r1 (ι₁ ∙ R) (ι₂ ∙ S) 
      ( ⊆in (λ a b z → cons-either (either.un z)) 
      , ⊆in (λ a b z → cons-either (either.un z)))

  ι₁-cancel : {A B C : Set}{R : Rel A B}{S : Rel C B}
            → either R S ∙ ι₁ ≡r R
  ι₁-cancel {R = R} {S = S} = ≡r-sym (coprod-uni-r1 R S ≡r-refl)

  ι₂-natural : {A B C D : Set}{R : Rel A B}{S : Rel C D}
             → ι₂ ∙ S ≡r (R + S) ∙ ι₂
  ι₂-natural {R = R} {S = S} 
    = coprod-uni-r2 (ι₁ ∙ R) (ι₂ ∙ S) 
      ( ⊆in (λ a b z → cons-either (either.un z))
      , ⊆in (λ a b z → cons-either (either.un z)))

  ι₂-cancel : {A B C : Set}{R : Rel A B}{S : Rel C B}
            → either R S ∙ ι₂ ≡r S
  ι₂-cancel {R = R} {S = S} = ≡r-sym (coprod-uni-r2 R S ≡r-refl)

  +-bi-functor : {A B C X Y Z : Set}
                 { R : Rel B C }{ H : Rel A B }
                 { S : Rel Y Z }{ I : Rel X Y }
               → (R + S) ∙ (H + I) ≡r (R ∙ H) + (S ∙ I)
  +-bi-functor {A} {B} {C} {X} {Y} {Z} {R} {H} {S} {I}
    = ⊆in aux1 , ⊆in aux2
    where
      aux1 : (a : A ⊎ X) (b : C ⊎ Z) → (R + S ∙ H + I) b a → ((R ∙ H) + (S ∙ I)) b a
      aux1 (i1 a) (i1 c) (i1 x , (cons-either (w1 , cons-fun q11 , q12) 
                                , cons-either (w2 , cons-fun q21 , q22))) 
           rewrite (i1-inj q21)
                 | (i1-inj q11) 
                 = cons-either (c , (cons-fun refl , x , (q12 , q22)))
      aux1 (i1 a) (i1 c) (i2 _ , (cons-either (_ , cons-fun () , _) , _))
      aux1 (i1 a) (i2 z) (i1 _ , (cons-either (_ , cons-fun () , _) , _))
      aux1 (i1 a) (i2 z) (i2 _ , (_ , cons-either (_ , cons-fun () , _)))
      aux1 (i2 x) (i1 c) (i2 _ , (cons-either (_ , cons-fun () , _) , _))
      aux1 (i2 x) (i1 c) (i1 _ , (_ , cons-either (_ , cons-fun () , _)))
      aux1 (i2 x) (i2 z) (i1 _ , (cons-either (_ , cons-fun (), _) , _))
      aux1 (i2 x) (i2 z) (i2 y , (cons-either (w1 , cons-fun q11 , q12) 
                                , cons-either (w2 , cons-fun q21 , q22))) 
           rewrite (i2-inj q21)
                 | (i2-inj q11)
                 = cons-either (z , ((cons-fun refl) , (y , (q12 , q22))))

      aux2 : (a : A ⊎ X) (b : C ⊎ Z) → ((R ∙ H) + (S ∙ I)) b a → (R + S ∙ H + I) b a
      aux2 (i1 a) (i1 c) (cons-either (w , (cons-fun q1 , rh))) rewrite (i1-inj q1) 
        = (i1 (p1∙ rh)) , ((cons-either (c , ((cons-fun refl) , (p1 $ p2∙ rh)))) , (cons-either ((p1∙ rh) , (cons-fun refl) , (p2 $ p2∙ rh))))
      aux2 (i1 a) (i2 z) (cons-either (_ , cons-fun () , _))
      aux2 (i2 x) (i1 c) (cons-either (_ , cons-fun () , _))
      aux2 (i2 x) (i2 z) (cons-either (w , (cons-fun q1 , rh))) rewrite (i2-inj q1) 
        = (i2 (p1∙ rh)) , ((cons-either (z , ((cons-fun refl) , (p1 $ p2∙ rh)))) , (cons-either ((p1∙ rh) , (cons-fun refl) , (p2 $ p2∙ rh))))

  +-ᵒ-distr : {A B C D : Set}{R : Rel A B}{S : Rel C D}
            → (R ᵒ + S ᵒ) ≡r (R + S) ᵒ
  +-ᵒ-distr {R = R} {S = S} 
    = ⊆in (λ { (i1 b) (i1 a) (cons-either (x , y , cons-ᵒ z))  → cons-ᵒ $ cons-either (b , cons-fun refl , subst (R b) (i1-inj (fun.un y)) z)
             ; (i2 _) (i1 _) (cons-either (_ , (cons-fun () , _)))
             ; (i1 _) (i2 _) (cons-either (_ , (cons-fun () , _)))
             ; (i2 d) (i2 c) (cons-either (x , y , cons-ᵒ z)) → cons-ᵒ $ cons-either (d , (cons-fun refl , subst (S d) (i2-inj (fun.un y)) z))
             }) 
    , ⊆in (λ { (i1 b) (i1 a) (cons-ᵒ (cons-either (x , y , z))) 
                   → cons-either (a , cons-fun refl , cons-ᵒ (subst (λ k → R k a) (i1-inj (fun.un y)) z))
             ; (i2 y) (i1 x) (cons-ᵒ (cons-either (_ , (cons-fun () , _))))
             ; (i1 _) (i2 _) (cons-ᵒ (cons-either (_ , (cons-fun () , _))))
             ; (i2 d) (i2 c) (cons-ᵒ (cons-either (x , y , z)))
                   → cons-either (c , cons-fun refl , cons-ᵒ (subst (λ k → S k c) (i2-inj (fun.un y)) z))
             })

  +-id : {A B : Set} → Id + Id ≡r Id {A ⊎ B}
  +-id {A} {B} = ⊆in aux1 , ⊆in aux2
    where
      aux1 : (a b : A ⊎ B) → (Id + Id) b a → Id b a
      aux1 (i1 x) b (cons-either (w , c)) 
        rewrite fun.un (p2 c) = cons-fun (fun.un (p1 c))
      aux1 (i2 y) b (cons-either (w , c)) 
        rewrite fun.un (p2 c) = cons-fun (fun.un (p1 c))

      aux2 : (a b : A ⊎ B) → Id b a → (Id + Id) b a
      aux2 a b (cons-fun un) rewrite un
        with b
      ...| i1 b′ = cons-either (b′ , cons-fun refl , cons-fun refl)
      ...| i2 b′ = cons-either (b′ , cons-fun refl , cons-fun refl)


  either-+-abs : {A B X Y Z : Set}{R : Rel X Z}{S : Rel Y Z}{T : Rel A X}{U : Rel B Y}
               → either R S ∙ (T + U) ≡r either (R ∙ T) (S ∙ U)
  either-+-abs = TODO
    where postulate TODO : ∀{a}{A : Set a} → A

  either-abs : {X Y Z K : Set}{R : Rel X Z}{S : Rel Y Z}{T : Rel Z K}
             → T ∙ either R S ≡r either (T ∙ R) (T ∙ S)
  either-abs = TODO
    where postulate TODO : ∀{a}{A : Set a} → A
