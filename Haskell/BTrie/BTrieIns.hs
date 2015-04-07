{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances  #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE UndecidableInstances  #-}
module BTrieIns where

import Data.Function (on)
import Data.Maybe
import Data.List (break, nub)

import Control.Monad
import Control.Applicative
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.List
import Control.Monad.Identity hiding (guard)
import qualified Data.Map as M

import BTrie
import Term

import Debug.Trace

-----------------------------------------------
-- Insertion

-- An important notion for insertion is that of reconstructing a cell
-- after inserting the term in a given position. We use zipper-like type:
type CellCtx i t c = BTrie i t c -> Cell i t c

-- We'll keep track of the number of labels we have in our Trie, in case we need
-- to create a few more and the current label, which might be Nothing, before
-- we find labels available.
type I = State (Int , Maybe Int)

------------------------------------
-- Usefull bunch of functions to handle our state.

getCount :: I Int
getCount = fst <$> get

getLbl   :: I (Maybe Int)
getLbl   = snd <$> get

putLbl l = modLbl (const $ Just l)
incCount = modCount (+1)
getIncCount = getCount >>= \r -> incCount >> return r
modCount f = modify (\(c , l) -> (f c , l))
modLbl   f = modify (\(c , l) -> (c , f l))
ite b t e = b >>= \x -> if x then t else e
  
  
-- Given a cell and an index, we return the new version of that cell
-- and the btrie to be traversed for the recursive arguments.
m :: (IsTrie i t c) => Cell i t c -> i -> I (CellCtx i t c , BTrie i t c)
m c tid = maybe (mIdxCtx c tid) (mSymCtx c) $ toSym tid

-- If the index we passed is NOT a binding symbol,
-- we need to take a look at our (idx -> trie) map.
-- Either we change it, by adding an entry to the empy trie there
-- or, we just traverse and do nothing.
mIdxCtx :: (IsTrie i t c)
        => Cell i t c -> i -> I (CellCtx i t c , BTrie i t c)
mIdxCtx (mh , bs) tid 
  = let mh' = M.alter (maybe (Just $ btrieEmptyInf) Just) tid mh
    in case M.lookup tid mh' of
            Nothing -> error "assumption"
            Just t' -> return (updateWith tid mh bs , t')

updateWith :: (IsTrie i t c) => i -> M.Map i (BTrie i t c)
           -> [(Int , Rs c)]
           -> CellCtx i t c
updateWith tid m bs bt = (M.insert tid bt m , bs)

-- If it is a symbol, it's a bit more tricky.
-- This symbol will either be registered in bs already, or not.
-- If it is registered, we just add a rule in that position.
-- If not, we insert it with a fresh rule.
--    
mSymCtx :: (IsTrie i t c)
        => Cell i t c -> Int -> I (CellCtx i t c , BTrie i t c)
mSymCtx (mh , bs) tsym
  = let bs' = M.fromList bs
    in case M.lookup tsym bs' of
            Nothing  -> makeRule 
              >>= \r -> return (const (mh , (tsym , [r]):bs), btrieEmptyInf)
            Just rs  -> handleRules rs
             >>= \r' -> return (const (mh , M.toList (M.insert tsym r' bs'))
                               , btrieEmptyInf)
  where
    -- When we find a symbol is already bound to a rule somewhere
    -- we need to see if we can use it, in anyway. That is,
    -- if we can apply some of the rules.
    --    If we can, nothing is done and we just change our state.
    --    If we canot, however,
    --      we get the current label, l, and generate a new one.
    --      We then add a rule (SigmaT l l') to that list and
    --      change our state to l', simulating the execution of that rule.
    --
    -- Note: when we start to generate symbols again, we never
    -- reuse a rule (the label does not belong to the trie! qed).
    -- handleRules :: Rs Term -> I (Rs Term)
    handleRules rs
      = let rsGather = filter isGather rs
      in do
        l <- getLbl
        case l of
          -- Ok, no label so far. 
          -- We make a Gather something, also for our state!
          Nothing -> if length rsGather > 0
                       then putLbl (fromGatherL rsGather) >> return rs
                       else (: rs) <$> makeRule
          
          -- If we have a label, we need to know if we can apply one of
          -- rs's rules or not, before choosing to create a new rule.
          Just l' -> if l' `elem` (rsImg rs)
                      then rsApp l' rs >> return rs
                      else (: rs) <$> makeRule
    
    fromGatherL (Gather g:_) = g
                 
    isGather (Gather _) = True
    isGather _          = False
          
    -- rsImg :: Rs Term -> [Int]
    rsImg = foldr (\h -> (ruleImg h ++)) []
      where
        ruleImg (SigmaT n _) = [n]
        ruleImg _            = []
        
    -- rsApp :: Int -> Rs Term -> I ()
    rsApp l ((SigmaT n m):rs)
      | l == n    = putLbl m
      | otherwise = rsApp l rs
    rsApp l (_:rs) = rsApp l rs
    
-- Makes a new rule. Already apply it to our state.
makeRule :: I (BRule c)
makeRule
  = do
    l <- getLbl
    case l of
      Nothing -> Gather <$> (getIncCount >>= \i -> putLbl i >> return i)
      Just l' -> getIncCount >>= \i -> putLbl i >> (return $ SigmaT l' i)

-- This is the actual insertion function.
-- We first insert labels and later we traverse the trie substituting
-- the last inserted rule for a SigmaF, final rule.    
insert :: (IsTrie i t c) => c -> t -> BTrieObj i t c -> BTrieObj i t c
insert c t (_ , Leaf r) = error "impossible trie;"
insert c t (count , bt)
  = let (bt', (i , j)) = runState (ins c t bt) (count , Nothing)
    in case j of
        -- Nothing -> error "something went really wrong..."
        Nothing -> (count , bt)
        Just j' -> (j' , substSigmaT j' c bt')
  where    
    substSigmaT :: (IsTrie i t c) => Int -> c -> BTrie i t c -> BTrie i t c
    substSigmaT k c bt = s k c bt
      where
        s k c (Leaf rs) = Leaf (map (sR k c) rs)
        s k c (Fork ms) = Fork (map (sC k c) ms)
        
        sR k c (SigmaT m n)
          | n == k = SigmaF m c k
          | otherwise = SigmaT m n
        sR _ _ r = r
        
        sC k c (mh , bs)
          = (M.map (substSigmaT k c) mh
            , map (\(i , rs) -> (i , map (sR k c) rs)) bs
            )  
      
-- Inserting a t in a BTrie has to start off by traversing a 1-cell
-- fork.    
ins :: (IsTrie i t c) => c -> t -> BTrie i t c -> I (BTrie i t c)
ins c t (Fork [cell])
  = Fork . (:[]) <$> insCell (open t) cell

-- Auxiliary function.
insCell :: (IsTrie i t c) => (i , [t]) -> Cell i t c
        -> I (Cell i t c)
insCell (tid , tr) cell
  = do
    (c' , bt) <- m cell tid
    -- The result of (m cell tid) is read of:
    -- the Cell with (tid , tr) is obtained by
    -- recursively inserting tr in bt and reconstructing
    -- with c'.
    case bt of
      -- Case bt is a Leaf, there's nothing else to do but to reconstruct the cell.
      Leaf r -> return $ c' (Leaf r)
      
      -- If it's a fork, however, there are a couple nuances.
      Fork btTarget
        -> case tr of
          -- We must make sure our tid is a NON-binding index.
          -- If that's the case, we add a new rule and a leaf.
          -- otherwise, the m function already took care of adding the rule
          -- and, in fact, c' = const bt', for some BTrie bt'.
          [] -> if (toSym tid == Nothing)
                 then makeRule >>= return . c' . Leaf . (:[])
                 else return $ c' (Fork [])
          
          -- If we have recursive arguments, however
          -- it's a simple matter of adding them one-by-one and 
          -- merging every resulting cell in a fork.
          tr -> case btTarget of
                 []  -> error "impossible by construction." -- m returns the infinite-cell fork
                                                            -- for the empty trie.
                 bts -> insCell' tr bts
                    >>= return . c' . Fork
  where
    -- list generalization of ins.
    insCell' :: (IsTrie i t c) => [t] -> [Cell i t c] -> I [Cell i t c]
    insCell' [] _  = return []
    insCell' _  [] = return []
    insCell' (t:ts) (b:bs)
      = (:) <$> insCell (open t) b <*> insCell' ts bs
  
  
  

