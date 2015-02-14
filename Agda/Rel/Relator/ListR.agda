{-# OPTIONS --guardedness-preserving-type-constructors #-}
open import Prelude
open import Coinduction

open import Rel.Core.Core
open import Rel.Core.Relator
open import Rel.Core.Equality

module Rel.Relator.ListR where
  
  -- TODO: Do I really need this terminating pragma here?
  --       The example in Coinduction.agda has no such annotaion.
  --       The proofs look nice, though.
  {-# TERMINATING #-}
  ListR : Set → Set
  ListR A = Unit ⊎ (A × Rec (♯ (ListR A)))

  nil : ∀{A} → ListR A
  nil = i1 unit

  cons : ∀{A} → (a : A) → (l : ListR A) → ListR A
  cons a l = i2 (a , fold l)

  pattern nilₚ = i1 unit
  pattern consₚ h t = i2 (h , fold t)

  ×-≡ : ∀{a}{A B : Set a}{a₁ a₂ : A}{b₁ b₂ : B}
      → a₁ ≡ a₂ → b₁ ≡ b₂ → _≡_ {a} {A × B} (a₁ , b₁) (a₂ , b₂)
  ×-≡ refl refl = refl

  instance
    isRelator-ListR : IsRelator ListR
    isRelator-ListR = record
      { Fᵣ = fr
      ; fmap-id = fr-id
      ; fmap-∙ = fr-∙
      ; fmap-ᵒ = fr-conv
      ; fmap-⊆ = fr-⊆
      } where
        fr : {A B : Set} → Rel A B → Rel (ListR A) (ListR B)
        fr r nilₚ nilₚ = Unit
        fr r nilₚ _    = ⊥
        fr r _ nilₚ    = ⊥
        fr r (consₚ b bs) (consₚ a as) 
                       = r b a × fr r bs as

        fr-id : {A : Set} → fr {A} {A} Id ≡r Id
        fr-id = ⊆in fr-id-1
              , ⊆in fr-id-2
            where
              fr-id-1 : {A : Set}(a b : ListR A) → fr Id b a → Id b a
              fr-id-1 nilₚ nilₚ rel = cons-fun refl
              fr-id-1 nilₚ (consₚ _ _) ()
              fr-id-1 (consₚ _ _) nilₚ ()
              fr-id-1 (consₚ a as) (consₚ b bs) (h , t) 
                = cons-fun (cong i2 (×-≡ (fun.un h) (cong fold $ fun.un (fr-id-1 as bs t))))

              fr-id-2 : {A : Set}(a b : ListR A) → Id b a → fr Id b a
              fr-id-2 nilₚ .nilₚ (cons-fun refl) 
                = unit
              fr-id-2 (consₚ a as) .(consₚ _ _) (cons-fun refl) 
                = cons-fun refl , fr-id-2 as as (cons-fun refl)

        fr-∙ : {A B C : Set} {R : Rel B C} {S : Rel A B}
             → fr (R ∙ S) ≡r fr R ∙ fr S
        fr-∙ = ⊆in fr-∙-1 , ⊆in fr-∙-2
          where
            fr-∙-1 : {A B C : Set} {R : Rel B C} {S : Rel A B}(a : ListR A) (b : ListR C) 
                   → fr (R ∙ S) b a → (fr R ∙ fr S) b a
            fr-∙-1 nilₚ nilₚ _ = i1 unit , unit , unit
            fr-∙-1 (consₚ _ _) nilₚ ()
            fr-∙-1 nilₚ (consₚ _ _) ()
            fr-∙-1 (consₚ a as) (consₚ c cs) ((h1 , h2) , hs)
              with fr-∙-1 as cs hs
            ...| (r1 , r2) = i2 (h1 , fold r1) , (p1 h2 , p1 r2) , p2 h2 , p2 r2

            fr-∙-2 : {A B C : Set} {R : Rel B C} {S : Rel A B}(a : ListR A) (b : ListR C) 
                    → (fr R ∙ fr S) b a → fr (R ∙ S) b a
            fr-∙-2 nilₚ nilₚ hip = unit
            fr-∙-2 (consₚ _ _) nilₚ (nilₚ , h2 , ())
            fr-∙-2 (consₚ _ _) nilₚ (consₚ _ _ , () , h3)
            fr-∙-2 nilₚ (consₚ _ _) (nilₚ , () , h3)
            fr-∙-2 nilₚ (consₚ _ _) (consₚ _ _ , h2 , ())
            fr-∙-2 (consₚ a as) (consₚ c cs) (nilₚ , () , ())
            fr-∙-2 (consₚ a as) (consₚ c cs) (consₚ b bs , h2 , h3) 
              = (b , p1 h2 , p1 h3) , fr-∙-2 as cs (bs , p2 h2 , p2 h3)

        fr-conv : {A B : Set} {R : Rel A B} → fr (R ᵒ) ≡r fr R ᵒ
        fr-conv = ⊆in fr-conv-1 , ⊆in fr-conv-2
          where
            fr-conv-1 : {A B : Set}{R : Rel A B}(a : ListR B) (b : ListR A) → fr (R ᵒ) b a → ((fr R) ᵒ) b a
            fr-conv-1 nilₚ nilₚ hip = unit
            fr-conv-1 (consₚ _ _) nilₚ ()
            fr-conv-1 nilₚ (consₚ _ _) ()
            fr-conv-1 (consₚ b bs) (consₚ a as) hip = p1 hip , fr-conv-1 bs as (p2 hip)

            fr-conv-2 : {A B : Set}{R : Rel A B}(a : ListR B) (b : ListR A) → ((fr R) ᵒ) b a → fr (R ᵒ) b a
            fr-conv-2 nilₚ nilₚ hip = unit
            fr-conv-2 (consₚ _ _) nilₚ ()
            fr-conv-2 nilₚ (consₚ _ _) ()
            fr-conv-2 (consₚ b bs) (consₚ a as) hip = p1 hip , fr-conv-2 bs as (p2 hip)

        fr-⊆ : {A B : Set} {R S : Rel A B} → R ⊆ S → fr R ⊆ fr S
        fr-⊆ rs = ⊆in (fr-sub rs)
          where
            fr-sub : {A B : Set}{R S : Rel A B} → R ⊆ S → (a : ListR A)(b : ListR B) → fr R b a → fr S b a
            fr-sub (⊆in rs) nilₚ nilₚ hip = unit
            fr-sub (⊆in rs) (consₚ _ _) nilₚ ()
            fr-sub (⊆in rs) nilₚ (consₚ _ _) ()
            fr-sub (⊆in rs) (consₚ a as) (consₚ b bs) hip = rs a b (p1 hip) , fr-sub (⊆in rs) as bs (p2 hip)
        
