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
  *-bi-functor = TODO
    where postulate TODO : {A : Set} → A

  *-ᵒ-distr : {A B C D : Set}{R : Rel A B}{S : Rel C D}
            → (R ᵒ * S ᵒ) ≡r (R * S) ᵒ
  *-ᵒ-distr {R = R} {S = S} 
    = ⊆in (λ { (b , d) (a , c) (cons-⟨,⟩ ((hb , h1 , cons-fun f) , (hd , h2 , cons-fun g))) 
           → cons-⟨,⟩ ((a , subst (λ x → R x a) (sym f) h1 , cons-fun refl) , (c , subst (λ x → S x c) (sym g) h2 , cons-fun refl)) })
    , ⊆in (λ { (b , d) (a , c) (cons-⟨,⟩ ((ha , h1 , cons-fun f) , (hc , h2 , cons-fun g))) 
           → cons-⟨,⟩ ((b , subst (R b) (sym f) h1 , cons-fun refl) , (d , subst (S d) (sym g) h2 , cons-fun refl)) })

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

  ι₂-natural : {A B C D : Set}{R : Rel A B}{S : Rel C D}
             → ι₂ ∙ S ≡r (R + S) ∙ ι₂
  ι₂-natural {R = R} {S = S} 
    = coprod-uni-r2 (ι₁ ∙ R) (ι₂ ∙ S) 
      ( ⊆in (λ a b z → cons-either (either.un z))
      , ⊆in (λ a b z → cons-either (either.un z)))

  +-bi-functor : {A B C X Y Z : Set}
                 { R : Rel B C }{ H : Rel A B }
                 { S : Rel Y Z }{ I : Rel X Y }
               → (R + S) ∙ (H + I) ≡r (R ∙ H) + (S ∙ I)
  +-bi-functor = TODO
    where postulate TODO : {A : Set} → A

  +-ᵒ-distr : {A B C D : Set}{R : Rel A B}{S : Rel C D}
            → (R ᵒ + S ᵒ) ≡r (R + S) ᵒ
  +-ᵒ-distr {R = R} {S = S} 
    = ⊆in (λ { (i1 b) (i1 a) (cons-either (x , y , z))  → cons-either (b , cons-fun refl , subst (R b) (i1-inj (fun.un y)) z)
             ; (i2 _) (i1 _) (cons-either (_ , (cons-fun () , _)))
             ; (i1 _) (i2 _) (cons-either (_ , (cons-fun () , _)))
             ; (i2 d) (i2 c) (cons-either (x , y , z)) → cons-either (d , (cons-fun refl , subst (S d) (i2-inj (fun.un y)) z))
             }) 
    , ⊆in (λ { (i1 b) (i1 a) (cons-either (x , y , z)) 
                   → cons-either (a , cons-fun refl , subst (λ k → R k a) (i1-inj (fun.un y)) z)
             ; (i2 y) (i1 x) (cons-either (_ , (cons-fun () , _)))
             ; (i1 _) (i2 _) (cons-either (_ , (cons-fun () , _)))
             ; (i2 d) (i2 c) (cons-either (x , y , z))
                   → cons-either (c , cons-fun refl , subst (λ k → S k c) (i2-inj (fun.un y)) z)
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
