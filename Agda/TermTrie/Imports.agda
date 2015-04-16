module TermTrie.Imports where

  open import Prelude hiding (_+_; _*_) renaming (either to +-elim)
    public

  open import Rel.Core hiding (map)
    public

  open import Rel.Core.Equality
    public

  open import Rel.Core.Product
    public

  open import Rel.Core.Coproduct
    public

  open import Rel.Properties.Basic
    public

  open import Rel.Properties.BiFunctor
    public

  -- open import Rel.Properties.Galois
  --  public

  open import Rel.Properties.Monotonicity
    public

  open import Rel.Properties.Idempotence
    public

  open import Rel.Properties.Neutral hiding (∙-id-l; ∙-id-r)
    public
