{-# OPTIONS --allow-unsolved-metas #-}
open import RW.Language.RTerm
open import RW.Language.RTermUtils
open import RW.Language.RTermIdx
open import RW.Data.RTrie

open import TermTrie.Imports

module TermTrie.TrieObj where

  add-action : Name → ℕ × RTrie → ℕ × RTrie
  add-action act bt
    = let
      ty = lift-ivar $ typeResult $ Ag2RType $ type act
    in insertTerm act ty bt

  myTrie : RTrie
  myTrie = p2
         -- $ add-action (quote ∙-assocl)
         -- $ add-action (quote ∙-assocr)
         $ add-action (quote ∙-assoc)
         -- $ add-action (quote ∙-assoc-join)
         $ add-action (quote ᵒ-idp)
         -- $ add-action (quote ᵒ-∙-distr)
         $ add-action (quote ∙-id-l)
         $ add-action (quote ∙-id-r)
         $ 0 , BTrieEmpty

  myTrieObj : RTrie
  myTrieObj = Fork
      (((Leaf [] ,
         (rappᵢ (rdef (quote _≡r_)) ,
          Fork
          (((Leaf [] ,
             (rappᵢ (rdef (quote _ᵒ)) ,
              Fork
              (((Leaf [] ,
                 (rappᵢ (rdef (quote _ᵒ)) ,
                  Fork (((Leaf [] , []) , (0 , Gr 6 ∷ []) ∷ []) ∷ []))
                 ∷ [])
                , [])
               ∷ []))
             ∷
             (rappᵢ (rdef (quote _∙_)) ,
              Fork
              (((Leaf [] ,
                 (rappᵢ (rdef (quote _∙_)) ,
                  Fork
                  (((Leaf [] , []) , (0 , Gr 8 ∷ []) ∷ []) ∷
                   ((Leaf [] , []) , (1 , Tr 8 9 ∷ []) ∷ []) ∷ []))
                 ∷ [])
                , [])
               ∷ ((Leaf [] , []) , (2 , Tr 9 10 ∷ []) ∷ []) ∷ []))
             ∷ [])
            , (0 , Gr 1 ∷ []) ∷ [])
           ∷
           ((Leaf [] ,
             (rappᵢ (rdef (quote _∙_)) ,
              Fork
              (((Leaf [] ,
                 (rappᵢ (rdef (quote fun)) ,
                  Fork
                  (((Leaf [] ,
                     (rlamᵢ , Fork (((Leaf (Tr 1 4 ∷ []) , []) , []) ∷ [])) ∷ [])
                    , [])
                   ∷ []))
                 ∷ [])
                , (0 , Tr 1 2 ∷ Tr 10 11 ∷ []) ∷ [])
               ∷
               ((Leaf [] ,
                 (rappᵢ (rdef (quote fun)) ,
                  Fork
                  (((Leaf [] ,
                     (rlamᵢ , Fork (((Leaf (Fr 2 (quote ∙-id-r) ∷ []) , []) , []) ∷ []))
                     ∷ [])
                    , [])
                   ∷ []))
                 ∷
                 (rappᵢ (rdef (quote _∙_)) ,
                  Fork
                  (((Leaf [] , []) , (1 , Tr 11 12 ∷ []) ∷ []) ∷
                   ((Leaf [] , []) , (2 , Fr 12 (quote ∙-assoc) ∷ []) ∷ []) ∷ []))
                 ∷ [])
                , (0 , Fr 4 (quote ∙-id-l) ∷ []) ∷ [])
               ∷ []))
             ∷ [])
            , (0 , Fr 6 (quote ᵒ-idp) ∷ []) ∷ [])
           ∷ []))
         ∷ [])
        , [])
       ∷ []) 

  replicateM : {A : Set} → List (Maybe A) → Maybe (List A)
  replicateM [] = just []
  replicateM (nothing ∷ _)  = nothing
  replicateM (just x  ∷ xs) with replicateM xs
  ...| just xs' = just (x ∷ xs')
  ...| nothing  = nothing
   
  search : AgTerm → List (List (ℕ × RTerm ⊥) × Name)
  search ag
    = let
      rt = forceBinary $ Ag2RTerm ag
    in maybe searchAux (([] , search-err) ∷ []) rt
    where
      postulate search-err : Name

      searchAux : RBinApp ⊥ → List (List (ℕ × RTerm ⊥) × Name)
      searchAux (hd , g₁ , g₂)
        = let
          g□ = g₁ ∩↑ g₂
          u₁ = g□ -↓ g₁
          u₂ = g□ -↓ g₂
          ul = (u₁ ∷ u₂ ∷ [])
        in maybe (λ l → lookupTerm (rapp hd l) myTrieObj
                        -- symmetric?!
                     ++ lookupTerm (rapp hd (reverse l)) myTrieObj)
                 [] (replicateM ul)
          

  open import Rel.Core
  open import Rel.Core.Correflexive

  twiceF : ℕ → ℕ
  twiceF zero    = zero
  twiceF (suc n) = suc (suc (twiceF n))

  twice : Rel ℕ ℕ
  twice = fun twiceF

  even : ℕ → Bool
  even zero          = true
  even (suc zero)    = false
  even (suc (suc n)) = even n

  So : Bool → Set
  So true  = Unit
  So false = ⊥

  evenR : Rel ℕ ℕ
  evenR = φ (So ∘ even)

  Goal : AgTerm
  Goal = pi
    (arg (arg-info visible relevant)
     (el (lit 0)
      (def (quote _⊆_)
       (arg (arg-info hidden relevant) (def (quote ℕ) []) ∷
        arg (arg-info hidden relevant) (def (quote ℕ) []) ∷
        arg (arg-info visible relevant)
        (def (quote _∙_)
         (arg (arg-info hidden relevant) (def (quote ℕ) []) ∷
          arg (arg-info hidden relevant) (def (quote ℕ) []) ∷
          arg (arg-info hidden relevant) (def (quote ℕ) []) ∷
          arg (arg-info visible relevant)
          (def (quote fun)
           (arg (arg-info hidden relevant) (def (quote ℕ) []) ∷
            arg (arg-info hidden relevant) (def (quote ℕ) []) ∷
            arg (arg-info visible relevant) (def (quote twice) []) ∷ []))
          ∷
          arg (arg-info visible relevant)
          (def (quote φ)
           (arg (arg-info hidden relevant) (def (quote ℕ) []) ∷
            arg (arg-info visible relevant)
            (lam visible
             (abs "x"
              (def (quote So)
               (arg (arg-info visible relevant)
                (def (quote even)
                 (arg (arg-info visible relevant) (var 0 []) ∷ []))
                ∷ []))))
            ∷ []))
          ∷ []))
        ∷
        arg (arg-info visible relevant)
        (def (quote _∙_)
         (arg (arg-info hidden relevant) (def (quote ℕ) []) ∷
          arg (arg-info hidden relevant) (def (quote ℕ) []) ∷
          arg (arg-info hidden relevant) (def (quote ℕ) []) ∷
          arg (arg-info visible relevant)
          (def (quote fun)
           (arg (arg-info hidden relevant) (def (quote ℕ) []) ∷
            arg (arg-info hidden relevant) (def (quote ℕ) []) ∷
            arg (arg-info visible relevant) (def (quote twice) []) ∷ []))
          ∷
          arg (arg-info visible relevant)
          (def (quote fun)
           (arg (arg-info hidden relevant) (def (quote ℕ) []) ∷
            arg (arg-info hidden relevant) (def (quote ℕ) []) ∷
            arg (arg-info visible relevant) (lam visible (abs "x" (var 0 [])))
            ∷ []))
          ∷ []))
        ∷ []))))
    (abs "_"
     (el (lit 0)
      (def (quote _⊆_)
       (arg (arg-info hidden relevant) (def (quote ℕ) []) ∷
        arg (arg-info hidden relevant) (def (quote ℕ) []) ∷
        arg (arg-info visible relevant)
        (def (quote _∙_)
         (arg (arg-info hidden relevant) (def (quote ℕ) []) ∷
          arg (arg-info hidden relevant) (def (quote ℕ) []) ∷
          arg (arg-info hidden relevant) (def (quote ℕ) []) ∷
          arg (arg-info visible relevant)
          (def (quote fun)
           (arg (arg-info hidden relevant) (def (quote ℕ) []) ∷
            arg (arg-info hidden relevant) (def (quote ℕ) []) ∷
            arg (arg-info visible relevant) (def (quote twice) []) ∷ []))
          ∷
          arg (arg-info visible relevant)
          (def (quote φ)
           (arg (arg-info hidden relevant) (def (quote ℕ) []) ∷
            arg (arg-info visible relevant)
            (lam visible
             (abs "x"
              (def (quote So)
               (arg (arg-info visible relevant)
                (def (quote even)
                 (arg (arg-info visible relevant) (var 0 []) ∷ []))
                ∷ []))))
            ∷ []))
          ∷ []))
        ∷
        arg (arg-info visible relevant)
        (def (quote fun)
         (arg (arg-info hidden relevant) (def (quote ℕ) []) ∷
          arg (arg-info hidden relevant) (def (quote ℕ) []) ∷
          arg (arg-info visible relevant) (def (quote twice) []) ∷ []))
        ∷ []))))

  term1 : RTerm ⊥
  term1 = rapp (rdef (quote _≡r_))
      (rapp (rdef (quote _∙_))
       (rapp (rdef (quote fun))
        (rapp (rdef (quote twice)) [] ∷ [])
        ∷ rapp (rdef (quote fun)) (rlam (ivar 0) ∷ []) ∷ [])
       ∷
       rapp (rdef (quote fun))
       (rapp (rdef (quote twice)) [] ∷ [])
       ∷ [])

  term1sym : RTerm ⊥
  term1sym = rapp (rdef (quote _≡r_))
      (rapp (rdef (quote fun))
       (rapp (rdef (quote twice)) [] ∷ [])
       ∷
       rapp (rdef (quote _∙_))
       (rapp (rdef (quote fun))
        (rapp (rdef (quote twice)) [] ∷ [])
        ∷ rapp (rdef (quote fun)) (rlam (ivar 0) ∷ []) ∷ [])
       ∷ [])

  !Just : ∀{a}{A : Set a} → Maybe A → A
  !Just (just a) = a
  !Just nothing  = blah
    where postulate blah : ∀{a}{A : Set a} → A

  test : ℕ
  test
    = let
      (hd , g₁ , g₂) = !Just $ forceBinary $ Ag2RTerm Goal
      g□ = g₁ ∩↑ g₂
      u₁ = !Just $ g□ -↓ g₁
      u₂ = !Just $ g□ -↓ g₂
      ul = (u₂ ∷ u₁ ∷ [])
      newT = rapp (rdef (quote _≡r_)) ul
    in {!lookupTerm newT myTrieObj!}
