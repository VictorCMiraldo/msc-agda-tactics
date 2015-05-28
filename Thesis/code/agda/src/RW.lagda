\begin{code}
open import Prelude
open import Data.Maybe using (Maybe; just; nothing)
open import Reflection renaming (Term to AgTerm; Type to AgType)
open import Data.String using (String)

open import RW.Language.RTerm
open import RW.Language.RTermUtils
open import RW.Language.FinTerm

open import RW.Strategy

open import RW.Utils.Monads
open import RW.Utils.Error
open Monad {{...}}
open IsError {{...}}
\end{code}

%<*module-decl>
\begin{code}
module RW (db : TStratDB) where
\end{code}
%</module-decl>

\begin{code}
-- We need to bring our instances into scope explicitely,
-- to make Agda happy.
private
  instance
    ErrErr   = IsError-StratErr
    ErrMonad = MonadError

  unarg : {A : Set} → Arg A → A
  unarg (arg _ x) = x
  
postulate
  RW-error : ∀{a}{A : Set a} → String → A
\end{code}

%<*ag2rtypefin-def>
\begin{code}
Ag2RTypeFin : AgType → ∃ FinTerm
Ag2RTypeFin = R2FinType ∘ lift-ivar ∘ η ∘ Ag2RType
\end{code}
%</ag2rtypefin-def>

%<*make-RWData-def>
\begin{code}
make-RWData : Name → AgTerm → List (Arg AgType) → Err StratErr RWData
make-RWData act goal ctx 
  with η (Ag2RTerm goal) | Ag2RTypeFin (type act) | map (Ag2RType ∘ unarg) ctx
...| g' | tyℕ , ty | ctx' with forceBinary g' | forceBinary (typeResult ty)
...| just g | just a = return (rw-data g tyℕ a ctx')
...| _ | _ = throwError (Custom "...")
\end{code}
%</make-RWData-def>

%<*RWErr-def>
\begin{code}
RWerr : Name → RWData → Err StratErr (RWData × UData × RTerm ⊥)
RWerr act d
  =   runUStrats d
  >>= λ u → runTStrats db d act u
  >>= λ v → return (d , u , v)
\end{code}
%</RWErr-def>

%<*by'-def>
\begin{code}
by' : Name → List (Arg AgType) → AgTerm → (RWData × UData × RTerm ⊥)
by' act ctx goal with runErr (make-RWData act goal ctx >>= RWerr act)
...| i1 err  = RW-error err
...| i2 term = term
\end{code}
%</by'-def>

%<*by-def>
\begin{code}
by : Name → List (Arg AgType) → AgTerm → AgTerm
by act ctx goal = R2AgTerm ∘ p2 ∘ p2 $ (by' act ctx goal)
\end{code}
%</by-def>

%<*by+-def>
\begin{code}
by+ : List Name → List (Arg AgType) → AgTerm → AgTerm
by+ [] _ _ = RW-error "No suitable action"
by+ (a ∷ as) ctx goal with runErr (make-RWData a goal ctx >>= RWerr a)
...| i1 _ = by+ as ctx goal
...| i2 t = R2AgTerm ∘ p2 ∘ p2 $ t
\end{code}
%</by+-def>

\begin{code}
open import RW.Data.RTrie
\end{code}

%<*auto-module-decl>
\begin{code}
module Auto 
    (bt    : RTrie)
    (newHd : RTermName → RTermName)
  where
\end{code}
%</auto-module-decl>

\begin{code}
  open import RW.Language.RTermTrie

  our-strategy : RTermName → Name → UData → Err StratErr (RTerm ⊥)
  our-strategy goal 
    = maybe 
      TStrat.how 
      (const $ const $ i1 no-strat) 
    $ filter-db db
    where
      no-strat : StratErr
      no-strat = NoTStrat goal (newHd goal)

      filter-db : TStratDB → Maybe TStrat
      filter-db [] = nothing
      filter-db (s ∷ ss) with TStrat.when s goal (newHd goal)
      ...| false = filter-db ss
      ...| true  = just s
\end{code}

%<*tactic-auto-internal>
\begin{code}
  auto-internal : List (Arg AgType) → AgTerm → Err StratErr AgTerm
  auto-internal _ goal with forceBinary $ Ag2RTerm goal
  ...| nothing = i1 $ Custom "non-binary goal"
  ...| just (hd , g₁ , g₂)
    = let
      options = search-action (newHd hd) (hd , g₁ , g₂) bt
      strat   = uncurry $ our-strategy hd
      err     = Custom "No option was succesful"
    in try-all strat err options >>= return ∘ R2AgTerm
\end{code}
%</tactic-auto-internal>
%<*tactic-auto>
\begin{code}
  auto : List (Arg AgType) → AgTerm → AgTerm
  auto ctx goal with runErr (auto-internal ctx goal)
  ...| i1 err = RW-error err
  ...| i2 r   = r
\end{code}
%</tactic-auto>
