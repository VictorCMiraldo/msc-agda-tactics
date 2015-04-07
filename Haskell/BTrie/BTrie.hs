{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances  #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE BangPatterns #-}
module BTrie where

import qualified Data.Map as M
import Text.PrettyPrint
import Control.DeepSeq

type family Idx t :: *

-- In order to be able to navigate a Trie indexed by a type t
-- we need a bit of machinery.
--
class (Eq t, Eq c , Ord idx , Show c) 
    => IsTrie idx t c | t -> idx , idx -> t , t -> c where  
    
  -- Since we have binding symbols, some of our indexes must correspond
  -- to these symbols.
  toSym :: idx -> Maybe Int
  fromSym :: Int -> idx
  
  -- And we must be able to open and close a type into it's index
  -- and respective recursive arguments.
  close :: (idx, [t]) -> t
  open  :: t -> (idx , [t])

-- Each cell (m , b) contains two partial maps. m is the map of non-binding indexes
-- into Tries where b is the map of binding indexes (symbols) into rules.
--  
type Cell idx t c = (M.Map idx (BTrie idx t c) , [(Int , Rs c)])

-- Rules specify how we rewrite labels and, eventually, reach conclusions c.
data BRule c
  = Gather Int
  | SigmaT Int Int
  | SigmaF Int c Int
  deriving (Eq, Show)
  
-- Type-synonym to simplify coding.
type Rs c = [BRule c]
  
-- A Trie is then defined by:
data BTrie :: * -> * -> * -> * where
  Fork :: (IsTrie idx t c) => [Cell idx t c]  -> BTrie idx t c
  Leaf :: (IsTrie idx t c) => [BRule c]       -> BTrie idx t c

-- The empty trie is defined by a Fork of an empty cell.
btrieEmpty :: (IsTrie i t c) => BTrie i t c
btrieEmpty = Fork $ [cellEmpty]
  where
    cellEmpty = (M.empty , [])
    
-- Or, to simplify insertion, by an infinite list of empty cells.
btrieEmptyInf :: (IsTrie i t c) => BTrie i t c
btrieEmptyInf = Fork $ repeat (M.empty , [])
  
-- conveniente substitution function.
subst :: (Eq c) => c -> c -> c -> c
subst c1 r c2
  | c1 == c2  = r
  | otherwise = c2
    
type Label c = Either Int c

type Env t = M.Map Int t

-- A BTrieObj is used for inserting. We need to keep track of how many labels we added so far.
-- Either this or we need a first traversal to count labels...
type BTrieObj idx t c = (Int , BTrie idx t c)

btrieObjEmpty :: (IsTrie i t c) => BTrieObj i t c
btrieObjEmpty = (0 , btrieEmpty)

---------------------------------------------
-- * Pretty printing

class (Show t , Show i , Show c , IsTrie i t c) => S i t c where

instance (S i t c) => Show (BTrie i t c) where
  show = render . ppr
  
pprRule :: Show a => BRule a -> Doc
pprRule (Gather n) = text "+" <+> text (show n)
pprRule (SigmaT n m)
  = text (show n) <+> text "-->" <+> text (show m)
pprRule (SigmaF n m _)
  = text (show n) <+> text "==>" <+> text (show m)
  
pprCell :: (S i t c) => Cell i t c -> Doc
pprCell (mh , bs) 
  = let mh' = M.toList mh
    in  vcat (map ((text "|" <+>) . pprIdx1) mh')
    $+$ vcat (map ((text "|" <+>) . pprBs1) bs)
    $+$ text "%"
  where
    pprIdx1 (tid , Leaf rs)
      = text (show tid) <+> text ":" <+> hcat (map pprRule rs)
    pprIdx1 (tid , bt)
      = text (show tid) <+> text ":"
      $+$ (nest 2 $ ppr bt)
      
    pprBs1 (i , r)
      = text (show i) <+> text "#"
        <+> vcat (map pprRule r)
  
ppr :: (S i t c) => BTrie i t c -> Doc
ppr (Leaf rs) = vcat (map pprRule rs)
ppr (Fork cs) = vcat (map pprCell cs)
  
----------------------------------------------
-- NFData instance

instance NFData (BTrie i t c) where rnf !_ = ()


