{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances  #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE UndecidableInstances  #-}
module Term where

import BTrie
import qualified Data.Map as M
import Data.Maybe (fromJust)
import Data.List (nub)

import Test.QuickCheck
import Control.Applicative
import Control.Monad

--------------------------
-- * Sample term language

type Name = String

data Term
  = Var Int
  | Lit Int
  | Lam Term
  | App String [Term]
  deriving (Eq, Show)
  
data TermCtx a
  = VarC Int
  | LitC Int
  | LamC (TermCtx a)
  | AppC String [TermCtx a]
  | Ctx a
  deriving (Eq , Show)
  
data TermId
  = VarId Int
  | LitId Int
  | LamId
  | AppId String
  deriving (Eq, Show, Ord)
  
--------------------------------
-- IsTrie Instance

-- Gets the identification of a term.
termId :: Term -> TermId
termId (Var i)   = VarId i
termId (Lit i)   = LitId i
termId (Lam _)   = LamId
termId (App n _) = AppId n

-- Gets the recursive arguments of a term.
termRec :: Term -> [Term]
termRec (Lam t)    = [t]
termRec (App _ ts) = ts
termRec _          = []

-- Opened variation of a term.
out :: Term -> (TermId , [Term])
out t = (termId t , termRec t)

type instance Idx Term = TermId

instance S TermId Term Name where

instance IsTrie TermId Term Name where
  -- type Idx Term = TermId
  -- type C Term   = Name
  
  toSym (VarId n) = Just n
  toSym _         = Nothing
  
  fromSym = VarId
  
  close (VarId i , []) = Var i
  close (LitId i , []) = Lit i
  close (LamId  , [t]) = Lam t
  close (AppId n , ts) = App n ts
  
  open = out
  
-------------------------------
-- Here are a few adaptations 
-- from RW.Language.TermUtils. 
 
intersect :: Term -> Term -> TermCtx ()
intersect (Var i) (Var j)
  | i == j    = VarC i
  | otherwise = Ctx ()
intersect (Lit i) (Lit j)
  | i == j    = LitC i
  | otherwise = Ctx ()
intersect (Lam t1) (Lam t2)
  = LamC $ intersect t1 t2
intersect (App a as) (App b bs)
  | a == b
    = let res = map (uncurry intersect) $ zip as bs
      in if all isHole res
          then Ctx ()
          else AppC a res
  | otherwise = Ctx ()
intersect _ _ = Ctx ()

isHole :: TermCtx a -> Bool
isHole (Ctx _) = True
isHole _       = False

intersectBinApp :: Term -> TermCtx ()
intersectBinApp (App _ [i , j])
  = intersect i j
  
subt :: TermCtx a -> Term -> Maybe [Term]
subt (Ctx _) t = Just [t]
subt (VarC i) (Var j)
  | i == j    = Just []
  | otherwise = Nothing
subt (LitC i) (Lit j)
  | i == j    = Just []
  | otherwise = Nothing
subt (LamC t) (Lam u) = subt t u
subt (AppC a as) (App b bs)
  | a == b = mapM (uncurry subt) (zip as bs) >>= return . concat
  | otherwise = Nothing
subt _ _ = Nothing

subt1 :: TermCtx a -> Term -> Maybe Term
subt1 ctx t
  | (Just (x:_)) <- subt ctx t = Just x
  | otherwise                  = Nothing

buildDiffFromBinap :: Term -> Term
buildDiffFromBinap (App n [i , j])
  = let ctx = i `intersect` j
        i'  = head $ fromJust $ subt ctx i
        j'  = head $ fromJust $ subt ctx j
    in App n [i' , j']
    
type Subst = M.Map Int Term
    
instantiate :: Term -> Term -> Subst -> Maybe Subst
instantiate (Var i) t s
  = case M.lookup i s of
      Just t' -> if t == t' then Just s
                            else Nothing
      Nothing -> Just $ M.insert i t s
instantiate (Lit j) (Lit k) s
  | j == k = Just s
  | otherwise = Nothing
instantiate (Lam t1) (Lam t2) s = instantiate t1 t2 s
instantiate (App a as) (App b bs) s
  | a == b    = instantiateList as bs s
  | otherwise = Nothing
instantiate _ _ _ = Nothing

instantiateList :: [Term] -> [Term] -> Subst -> Maybe Subst
instantiateList [] [] s = Just s
instantiateList (_:_) [] _ = Nothing
instantiateList [] (_:_) _ = Nothing
instantiateList (a:as) (b:bs) s
  = instantiate a b s >>= instantiateList as bs
  
inst :: Term -> Term -> Maybe Subst
inst t1 t2 = instantiate t1 t2 M.empty

