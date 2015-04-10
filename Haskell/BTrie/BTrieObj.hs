module BTrieObj where

import BTrie
import Term
import TermGen
import qualified Data.Map as M
import BTrieLkup
import BTrieIns

import Control.Monad
import Control.Applicative
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.List
import Control.Monad.Identity hiding (guard)

------------------------------------------------------------------------------------------
-- A Sample TermTrie

myTrie :: BTrie TermId Term Name
myTrie = Fork [(root , [])]
  where
    root = M.singleton (AppId "==") t1
    
    t1 = Fork [ (M.singleton (AppId "+") t1l , [])
              , (M.singleton (AppId "+") t1rr
                , [(0 , [(SigmaF 3 "RI" 1)])]
                )
              ]
   
    t1l = Fork 
        [ (M.empty
          , [(0 , [Gather 1]) , (2 , [Gather 2])]
          )
        , (M.fromList [(AppId "+", t1lr) , (LitId 0 , Leaf $ [SigmaT 1 3])]
          , [(1 , [SigmaT 1 4])]
          )
        ]
        
    t1lr = Fork [ (M.empty
                  , [(1 , [SigmaT 2 5])] -- l3
                  )
                , (M.empty
                  , [(0 , [SigmaT 5 6])] -- l3
                  )
                ]
                
    t1rr = Fork 
           [ (M.singleton (AppId "+") t1rrl
             , [(1 , [SigmaT 4 7])]
             )
           , (M.empty , [(0 , [SigmaF 7 "COMM" 2])])
           ]
            
    t1rrl = Fork [ (M.empty , [(2, [SigmaT 6 8])])
                 , (M.empty , [(1, [SigmaF 8 "ASSOC" 3])])
                 ] 
                 
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
  
myTrie2Obj
  = insert "SQN" lemma_sq1
  $ insert "RN" lemma_sum_inv
  $ insert "MI" lemma_mul_id
  $ insert "MI" lemma_mul0
  $ insert "SQ" lemma_sq 
  $ insert "DIST" lemma_dist
  $ insert "MUL2" lemma_mul2 (9 , myTrie)
  
myTrie3Obj 0 = return myTrie2Obj
myTrie3Obj n 
  = do
    (name , lemma) <- genLemma
    tt            <- myTrie3Obj (n-1)
    return $ insert name lemma tt
    
myTrie2
  = snd myTrie2Obj
  
mlkup t@(App _ [_ , _]) bt = lkup (buildDiffFromBinap t) bt
mlkup _ _ = error "Binary applications only!"

t1 :: Term
t1 = App "==" [App "+" [Var 0 , Lit 0] , Var 0]

t2 :: Term
t2 = App "==" [App "+" [App "+" [Var 3 , Lit 0] , Var 1] , App "+" [Var 3 , Var 1]] 

t3 :: Term
t3 = App "==" [App "+" [App "+" [Var 1, Var 0] , Lit 0]
              , App "+" [Var 1 , Var 0]
              ]

t4 :: Term
t4 = App "==" [App "+" [Lit 1 , Lit 0]
              ,App "+" [Lit 0 , Lit 1]
              ]
              
t5 :: Term
t5 = App "=="
  [ App "+"
    [ Var 0
    , App "+" 
      [ App "*" [Var 1 , Lit 0]
      , Var 2
      ]
    ]
  , App "+"
    [ App "+" 
      [ Var 0
      , App "*" [Var 1 , Lit 0]
      ]
    , Var 2
    ]
  ] 
  
t6 :: Term
t6 = App "=="
  [ App "*" [App "+" [Var 0 , Lit 5] , Lit 3] 
  , App "*" [App "+" [Lit 5 , Var 0] , Lit 3]
  ]
  
----------------------------------
-- Ivar testing

lemma_ri_ivar :: Term
lemma_ri_ivar = App "=="
  [ App "+" [ Var 0 , Lit 0 ]
  , Var 0
  ]
  
myTrieIvar
  = insert "RI" lemma_ri_ivar
  $ insert "RN" lemma_sum_inv
  $ insert "MI" lemma_mul_id
  $ insert "MN" lemma_mul0
  $ btrieObjEmpty
  
testTerm :: Term
testTerm = App "=="
  [ App "*" [Var 0 , App "+" [ App "%" [Var 1 , Lit 5 ] , Lit 0]] 
  , App "*" [Var 0 , App "%" [Var 1 , Lit 5]]
  ]
