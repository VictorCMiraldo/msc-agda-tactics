{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances  #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE UndecidableInstances  #-}
module BTrieLkup where

import Data.Function (on)
import Data.Maybe
import Data.List (break, nub, (\\))

import Control.Monad
import Control.Applicative
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.List
import Control.Monad.Identity hiding (guard)
import qualified Data.Map as M

import BTrie

import Debug.Trace
import Unsafe.Coerce

import Term


type List = ListT Identity

unList :: List a -> [a]
unList = runIdentity . runListT

--------------------------
-- A single state consists of a map of variables into terms
-- and a list of conclusions.

data BST t c = BST
  { env :: Env t
  , lbl :: Maybe (Label c)
  }
  
--------------------------------------
-- Debugging instances
  
printEnvs :: [BST t c] -> String
printEnvs e = let e' = unsafeCoerce e :: [BST Term Name]
              in unlines $ map aux e'
  where
    aux (BST e lbl) = show e ++ "\n\t" ++ show lbl
  
  
---------------------------------------
-- Managing BSTs
  
instance (IsTrie i t c) => Eq (BST t c) where
  (BST e1 l1) == (BST e2 l2)
    = e1 == e2 && l2 == l2
    
modifyEnv :: (Env t -> Env t) -> BST t c -> BST t c
modifyEnv f (BST e l) = BST (f e) l
  
bstEmpty :: BST t c
bstEmpty = BST M.empty Nothing

bstOpen :: BST t c -> (Env t , Maybe c)
bstOpen (BST e l) = (e , lbljoin l)
  where  
    lbljoin :: Maybe (Label a) -> Maybe a
    lbljoin (Just (Right a)) = Just a
    lbljoin _                = Nothing
    
---------------------------------------------
-- Looking something up

-- Our lookup type is a reader on a list of configurations,
-- to a list of still possible configurations.
type B t c = Reader [BST t c]

-- Applies a rule to all states.
applyBRule :: (IsTrie i t c) => BRule c -> B t c [BST t c]
applyBRule r
  = do
    bst <- ask
    return [ applyBRule1 r b | b <- bst ]

applyBRule1 :: (IsTrie i t c) => BRule c -> BST t c -> BST t c
applyBRule1 (Gather n)     (BST e _) 
  = BST e $ Just (Left n)
  
applyBRule1 (SigmaT m n)   (BST e (Just k)) 
  | Left m == k  = BST e (Just (Left n))
  | otherwise    = BST e Nothing 
  
applyBRule1 (SigmaF m c k) (BST e (Just k')) 
  | Left m == k' = BST e $ Just (Right c)
  | otherwise    = BST e $ Nothing
  
applyBRule1 _ (BST e _) = BST e Nothing

-- Applies a given list of rules to the possible states.
ruleList :: (IsTrie i t c) => Rs c -> B t c [BST t c]
ruleList rs = concat <$> mapM applyBRule rs

-- Interface lvl lookup function.
lkup :: (IsTrie i t c) => t -> BTrie i t c -> [(Env t , c)]
lkup t bt = nub $ accept $ map bstOpen $ runReader (lkupAux t bt) [bstEmpty]
  where
    accept :: [(Env t , Maybe c)] -> [(Env t , c)]
    accept []                  = []
    accept ((a , Just b) : hs) = (a , b) : accept hs
    accept ((_ , Nothing): hs) = accept hs
                                   
bAssert :: (IsTrie i t c) => Bool -> B t c [a] -> B t c [a]
bAssert False _ = return []
bAssert True m  = m

-- This is where the real lokup happens.
lkupAux :: (IsTrie i t c) => t -> BTrie i t c -> B t c [BST t c]
-- if we get to a leaf here, our lookup fails.
lkupAux t (Leaf r) = return []
-- If we get to a 1-cell fork, however,
lkupAux t root@(Fork [(rs , bs)])
  = let (tid , tr) = open t
  in (++) <$> lkupInst t bs -- we can either instantiate one of the variables in bs with t
          <*> case M.lookup tid rs of
                -- or lookup the corresponding term id in rs.
                Nothing -> return []
                
                -- If we find a leaf, and we also don't have anymore recursive arguments
                -- it's a simple matter of applying that list of rules.
                Just (Leaf r) -> bAssert (tr == []) 
                               $ ruleList r
                
                -- If we get to a fork, we need to lookup every recursive argument
                -- in each corresponding cell of the fork.
                Just (Fork ms)-> bAssert (length tr == length ms) 
                               $ lkupList $ zip tr ms

lkupAux t (Fork ms) = error "..."

lkupList :: (IsTrie i t c) 
         => [(t , (M.Map i (BTrie i t c) , [(Int , Rs c)]))]
         -> B t c [BST t c]
lkupList [] = ask
lkupList ((t , (mh , bs)):ts)
  = do 
    -- we're giving access to what happened on the left of
    -- a cell, before concluding what will happen.
    s1 <- lkupAux t r'
    s2 <- local (++ s1) $ lkupList ts
    return $ s1 ++ s2
  where
    r' = Fork [(mh , bs)]

mapFilter :: (b -> Bool) -> (a -> b) -> [a] -> [b]
mapFilter p f = foldr (\h r -> let x = f h in 
                                if p x then x:r else r) [] 
 
-- Instantiation is simple.
-- Given a pair (s , r) of a variable s to be instantiated and a list r of rules,
-- we add the binding s = t in all envs where s is unbound.
-- later we filter out all envs where s corresponds to a different term than t.   
lkupInst :: (IsTrie i t c) => t -> [(Int, Rs c)] -> B t c [BST t c]
lkupInst t [] = return []
lkupInst t ((s , r):rs)
  = (++) <$> tr s r t <*> lkupInst t rs
  where
    -- tr s r t = mapFilter (isValid s t) (applyBRule1 r . addUnbound s t) <$> ask
    tr s r t = mapFilter (isValid s t) (addUnbound s t) <$> ruleList r
  
    -- we add (s , t) to (env st) if M.lookup s returns nothing. 
    -- We leave the envoirements where s is already bound untouched.
    addUnbound s t st = st { env = M.alter (maybe (Just t) Just) s (env st) }
    
    -- 
    isValid s t st = M.lookup s (env st) == Just t
    
  
    
    
      
