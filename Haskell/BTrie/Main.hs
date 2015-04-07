module Main where

import BTrie
import BTrieIns
import BTrieLkup
import Term
import TermGen

import Control.Monad
import Control.Applicative
import Test.QuickCheck
import Data.Char (isUpper)

import System.Environment
import System.Random
import System.CPUTime
import Data.Time.Clock.POSIX
import Text.Printf
import Control.DeepSeq
import qualified Data.Map as M

--------------------------------
-- List shuffling
 
fisherYatesStep :: RandomGen g => (M.Map Int a, g) -> (Int, a) -> (M.Map Int a, g)
fisherYatesStep (m, gen) (i, x) = ((M.insert j x . M.insert i (m M.! j)) m, gen')
  where
    (j, gen') = randomR (0, i) gen
 
fisherYates :: RandomGen g => g -> [a] -> ([a], g)
fisherYates gen [] = ([], gen)
fisherYates gen l = 
  toElems $ foldl fisherYatesStep (initial (head l) gen) (numerate (tail l))
  where
    toElems (x, y) = (M.elems x, y)
    numerate = zip [1..]
    initial x gen = (M.singleton 0 x, gen)
    
shuffle :: [a] -> IO [a]
shuffle l
  = do
    gen <- mkStdGen . fromInteger <$> getCPUTime
    let l'  = fisherYates gen l
    return $ fst l'
    
------------------------------------------------------
-- Lemmas

lemma_ri :: Term
lemma_ri 
  = App "==" [App "+" [Var 0 , Lit 0], Var 0]

lemma_comm :: Term
lemma_comm 
  = App "==" [App "+" [Var 0 , Var 1] , App "+" [Var 1 , Var 0]]
  
lemma_mul2 :: Term
lemma_mul2 = App "=="
  [ App "*" [Lit 2 , Var 0]
  , App "+" [Var 0 , Var 0]
  ]
  
lemma_sq :: Term
lemma_sq = App "=="
  [ App "*" [Var 0 , Var 0]
  , App "^" [Var 0 , Lit 2]
  ]
  
lemma_sq1 :: Term
lemma_sq1 = App "=="
  [ App "^" [Var 0 , Lit 0]
  , Lit 1
  ]
  
lemma_dist :: Term
lemma_dist = App "=="
  [ App "*" [App "+" [Var 0 , Var 1] , App "+" [Var 2 , Var 3]]
  , App "+" [App "*" [Var 0 , Var 2] , App "*" [Var 1 , Var 3]]
  ]
  
lemma_mul0 :: Term
lemma_mul0 = App "=="
  [ App "*" [Var 0 , Lit 0]
  , Lit 0
  ]
  
lemma_mul_id :: Term
lemma_mul_id = App "=="
  [ App "*" [Var 0 , Lit 1]
  , Var 0
  ]
  
lemma_sum_inv :: Term
lemma_sum_inv = App "=="
  [ App "+" [Var 0 , App "-" [Var 0]]
  , Lit 0
  ]
  
lemmaList :: [(Name , Term)]
lemmaList
  = [ ("RI"   , lemma_ri)
    , ("COMM" , lemma_comm)
    , ("MUL2" , lemma_mul2)
    , ("SQ"   , lemma_sq)
    , ("SQ1"  , lemma_sq1)
    , ("DIST" , lemma_dist)
    , ("MUL0" , lemma_mul0)
    , ("MI"   , lemma_mul_id)
    , ("SINV" , lemma_sum_inv)
    ] 
    
printLemmas = mapM (putStrLn . showLemma) lemmaList
  where
    showLemma (s , l)
      = s ++ "\n\t" ++ show l
      
printDistribution l = mapM (putChar . tr . head . fst) l >> putChar '\n'
  where
    tr c 
      | isUpper c = c
      | otherwise = '.'
    
-------------------------------------------------------
-- Rewrite library

-- This is how we are currently doing a rewrite.
-- Given a goal and a list of actions, maybe we can apply one!
currentRW :: Term -> [(String , Term)] -> Maybe String
currentRW t@(App "==" [g1 , g2]) (a:as)
  = rw1 g1 g2 a `mplus` currentRW t as
  where
    rw1 g1 g2 (act , App "==" [ty1 , ty2])
      = let gSQ = intersect g1 g2
            u1  = subt1 gSQ g1 >>= inst ty1
            u2  = subt1 gSQ g2 >>= inst ty2
        in case (u1 , u2) of
            (Just _ , Just _) -> Just act
            _                 -> Nothing
currentRW _ _ = Nothing
     
-- This is the efficient version of the above...       
efficientRW :: Term -> BTrie TermId Term Name -> Maybe String
efficientRW t bt = fix $ lkup (buildDiffFromBinap t) bt
  where
    fix [] = Nothing
    fix (h:_) = Just $ snd h
    
    
data A = A { mx :: Int , pr :: Bool }
    
handleArgs :: [String] -> A
handleArgs []           = A 0 False
handleArgs ("max":n:as) = (handleArgs as) { mx = read n }
handleArgs ("print":as) = (handleArgs as) { pr  = True }

main :: IO ()
main 
  = do
    args <- getArgs
    let (A max printFlag) = handleArgs args
    printLemmas
    putStrLn $ "!! Generating " ++ show max ++ " dummy insertions."
    dummyLemmas <- replicateM max $ (generate genLemma)
    l <- shuffle $ lemmaList ++ dummyLemmas
    
    when printFlag $ printDistribution l
    
    putStrLn "!! Building Trie"
    bti <- getCPUTime
    let bt = foldr (uncurry insert) btrieObjEmpty l
    deepseq bt $ return ()
    btf <- getCPUTime
    printDiff bti btf
    
    putStrLn "!! Generating term"
    skel <- generate $ elements lemmaList
    goal <- generate $ genTermFor (snd skel)
    when printFlag
      $ putStrLn $ "\t[" ++ fst skel ++ "] " ++ show goal
    
    putStrLn "!! Naive term search: "
    ni <- getCPUTime
    let res = currentRW goal l
    deepseq res $ return ()
    nf <- getCPUTime
    printDiff ni nf
    
    
    putStrLn $ "\t" ++ show res
    
    putStrLn "!! BTrie term search: "
    bi <- getCPUTime
    let res2 = efficientRW goal (snd bt)
    deepseq res2 $ return ()
    bf <- getCPUTime
    printDiff bi bf
    putStrLn $ "\t" ++ show res2
    
printDiff i f
  = let btdiff = (fromIntegral (f - i)) / (10^12)
    in printf "@ %0.9f sec\n" (btdiff :: Double)
