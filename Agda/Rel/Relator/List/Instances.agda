open import Prelude hiding (_*_; _+_; _++_) renaming (either to +-elim)

open import Rel.Core
open import Rel.Core.Equality
open import Rel.Core.Product
open import Rel.Core.Coproduct
open import Rel.Relator
open import Rel.Relator.List

-- Does not typecheck without marking isDec-cataL as terminating.
-- Last time I tried with 2.5GB of heap and 64MB of stack.
--
-- 
--
-- agda: Heap exhausted;
-- Current maximum heap size is 2684354560 bytes (2560 MB);
-- use `+RTS -M<size>' to increase it.
--   27,037,886,984 bytes allocated in the heap
--    7,623,372,984 bytes copied during GC
--   2,643,192,104 bytes maximum residency (20 sample(s))
--       12,916,504 bytes maximum slop
--             2675 MB total memory in use (19 MB lost due to fragmentation)
--
--                                     Tot time (elapsed)  Avg pause  Max pause
--   Gen  0     51388 colls,     0 par   16.42s   16.44s     0.0003s    0.0033s
--   Gen  1        20 colls,     0 par   55.17s   55.25s     2.7623s    17.1653s
-- 
--  INIT    time    0.00s  (  0.00s elapsed)
--  MUT     time   70.43s  ( 70.53s elapsed)
--  GC      time   71.59s  ( 71.69s elapsed)
--  EXIT    time    0.00s  (  0.00s elapsed)
--  Total   time  142.02s  (142.22s elapsed)
--
--  %GC     time      50.4%  (50.4% elapsed)
--
--  Alloc rate    383,871,836 bytes per MUT second
--
--  Productivity  49.6% of total user, 49.5% of total elapsed
--


module Rel.Relator.List.Instances where

  open IsWFunctor1 {{...}}
  open IsDec       {{...}}

  instance
    -- L's action on arrows is decidable, as long the target arrow R is decidable and A has decidable equality.
    isDec-L : {X Y A : Set}{R : Rel X Y}{{ dR : IsDec R }}{{ eqA : Eq A }}
            → IsDec (Fᵣ {F = L} {X = A} R)
    isDec-L {X} {Y} {A} {R} {{dec dR}} {{eq _≟-A_ }} = dec aux
      where
        aux : (y : L A Y)(x : L A X) → Dec ((Id + (Id * R)) y x)
        aux (i1 unit) (i1 unit) = yes (cons-either (unit , ((cons-fun refl) , cons-fun refl)))
        aux (i2 _) (i1 _) = no (λ { (cons-either (w , cons-fun () , q)) })
        aux (i1 _) (i2 _) = no (λ { (cons-either (w , cons-fun () , q)) })
        aux (i2 (ay , y)) (i2 (ax , x)) with ay ≟-A ax | dR y x
        ...| yes ay≡ax | yes xRy = yes (cons-either ((ay , y) , ((cons-fun refl) 
                                 , (cons-⟨,⟩ ((ay , ((cons-fun refl) , cons-fun (sym ay≡ax))) , x , (xRy , (cons-fun refl)))))))
        ...| no  ay≢ax | yes xRy = no (λ { (cons-either (.(ay , y) , cons-fun refl , cons-⟨,⟩ ((.ay , cons-fun refl , r) , k2))) 
                                       → ay≢ax (sym $ fun.un r) })
        ...| yes ay≡ax | no ¬xRy = no (λ { (cons-either (.(ay , y) , cons-fun refl , cons-⟨,⟩ (_ , .x , q , cons-fun refl))) 
                                       → ¬xRy q })
        ...| no  ay≢ax | no ¬xRy = no (λ { (cons-either (.(ay , y) , cons-fun refl , cons-⟨,⟩ ((.ay , cons-fun refl , r) , k2))) 
                                       → ay≢ax (sym $ fun.un r) }) 


    -- If we can decide (read compute) the composition of R and Fᵣ ⟦ R ⟧₁, 
    -- then list catamorphisms of decidable relations are still decidable! :)
    --
    -- The 'composability' restriction is imposed to provide a way to 'choose'
    -- an intermediate b for the induction step.
    -- It arises from a simple derivation:
    --
    --      b ⟦ R ⟧ (a ∷ as)
    --   ≡  b (⟦ R ⟧ ∙ inL ∙ ι₂) (a , as)
    --   ≡  b (R ∙ Fᵣ ⟦ R ⟧ ∙ ι₂) (a , as)
    --   ≡  b (R ∙ (Id + Id * ⟦ R ⟧) ∙ ι₂) (a , as)
    --   ≡  b ((R ∙ ι₂) ∙ (Id * ⟦ R ⟧)) (a , as)
    --                  ↑ 
    --
    -- We need to be able to 'choose' a b′ from the indicated composition!
    --
    {-# TERMINATING #-}
    isDec-cataL : {A B : Set}{R : Rel (L A B) B}{{ dR : IsDec R }}{{ c : Composes (R ∙ ι₂) (Id * ⟦ R ⟧₁) }}
                → IsDec ⟦ R ⟧₁
    isDec-cataL {A} {B} {R} {{ dec dR }} {{ fc , prfc }} = dec decide
      where
        decide : (b : B)(l : μ L A) → Dec (⟦ R ⟧₁ b l)
        decide b (sup (i1 unit) _) with dR b (i1 unit)
        ...| yes y = yes (cons-cata ((i1 unit) , (y , (cons-either (unit , ((cons-fun refl) , (cons-fun refl)))))))
        ...| no  n = no (λ { (cons-cata (.(i1 unit) , (r , (cons-either (.unit , cons-fun refl , cons-fun refl))))) 
                         → n r })
        decide b (sup (i2 a) x) with fc b (a , x unit) | prfc b (a , x unit)
        ...| (.a , b') | q1 , cons-⟨,⟩ ((.a , cons-fun refl , cons-fun refl) , .(x unit) , q2 , cons-fun refl) 
          = decAux q2 (subst (R b) (sym $ fun.un $ p2 $ p2∙ q1) (p1 $ p2∙ q1)) (decide b' (x unit)) (dR b (i2 (a , b')))
          where 
            decAux : (p1 : ⟦ R ⟧₁ b' (x unit))(p2 : R b (i2 (a , b')))
                   → Dec (⟦ R ⟧₁ b' (x unit)) → Dec (R b (i2 (a , b')))
                   → Dec (⟦ R ⟧₁ b (sup (i2 a) x))
            decAux p2 p3 (yes _) (yes _) = yes (cons-cata ((i2 (a , b')) , (p3 , (cons-either ((a , b') , ((cons-fun refl) 
                                               , (cons-⟨,⟩ ((a , ((cons-fun refl) , (cons-fun refl))) 
                                               , ((x unit) , ((⟦_⟧₁.un p2) , (cons-fun refl)))))))))))
            decAux p2 p3 (yes _) (no ¬q) = no (const (¬q p3))
            decAux p2 p3 (no ¬p) _       = no (const (¬p p2))
