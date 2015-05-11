open import Prelude hiding (_+_; _*_) renaming (either to +-elim)

open import RW.Language.RTerm
open import RW.Data.RTrie
open import RW.Language.RTermTrie

open import Rel.Core
open import Rel.Core.Equality
open import Rel.Core.Product
open import Rel.Core.Coproduct
open import Rel.Properties.Basic
open import Rel.Properties.BiFunctor
open import Rel.Properties.Idempotence
open import Rel.Properties.Neutral hiding (∙-id-l; ∙-id-r)

module Rel.Properties.Database where

  db : RTrie
  db = unquote (quoteTerm (p2
     $ add-action (quote ∪-uni-l)
     $ add-action (quote ∪-uni-r)
     $ add-action (quote ∩-uni-l)
     $ add-action (quote ∩-uni-r)
     $ add-action (quote prod-uni-r1)
     $ add-action (quote prod-uni-r2)
     $ add-action (quote prod-uni-l)
     $ add-action (quote coprod-uni-r1)
     $ add-action (quote coprod-uni-r2)
     $ add-action (quote coprod-uni-l)
     $ add-action (quote ∙-assoc)
     $ add-action (quote ∙-assoc-join)
     $ add-action (quote ᵒ-idp)
     $ add-action (quote ᵒ-∙-distr)
     $ add-action (quote ∙-id-l)
     $ add-action (quote ∙-id-r)
     $ add-action (quote π₁-natural)
     $ add-action (quote π₂-natural)
     $ add-action (quote *-bi-functor)
     $ add-action (quote *-ᵒ-distr)
     $ add-action (quote *-id)
     $ add-action (quote ι₁-natural)
     $ add-action (quote ι₁-cancel)
     $ add-action (quote ι₂-natural)
     $ add-action (quote ι₂-cancel)
     $ add-action (quote +-bi-functor)
     $ add-action (quote +-ᵒ-distr)
     $ add-action (quote +-id)
     $ add-action (quote either-+-abs)
     $ add-action (quote either-abs)
     $ 0 , BTrieEmpty))
