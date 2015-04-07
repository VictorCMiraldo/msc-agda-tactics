module TermGen where

import qualified Data.Map as M
import Data.Maybe (fromJust)
import Data.List (nub)

import Test.QuickCheck
import Control.Applicative
import Control.Monad

import Term

-----------------------------------------
-- Arbitrary Instances
  
  
-- Here we use different names to prevent overlapping definitions.
-- After all, we could generate "+-right-identity".
opTable :: [(String , Int)]
opTable =
  [( ".+" , 2 )
  ,( ".*" , 2 )
  ,( ".-" , 2 )
  ,( "./" , 2 )
  ,( ".^" , 2 )
  ,( ".if" , 3)
  ,( ".sin" , 1)
  ,( ".cos" , 1)
  ,( ".tan" , 1)
  ,( ".%" , 2)
  ]
  
arity :: String -> Int
arity s = maybe (0-1) id $ M.lookup s (M.fromList opTable)
  
ops :: [String]
ops = map fst opTable

genN :: Int -> Gen Int
genN i = elements [i]

-- Given a var range, generates a TermId
genTermId :: Int -> Gen TermId
genTermId varRange
  = do
    i <- frequency $ zip freqs gens
    case i of
      1 -> VarId <$> choose (0 , varRange)
      2 -> LitId <$> arbitrary `suchThat` (>= 0)
      3 -> return LamId
      4 -> AppId <$> elements ops
      _ -> error "impossible"
  where
    gens = map genN [1..4]
    freqs = [15 , 25 , 5 , 35]

instance Arbitrary TermId where
  arbitrary = genTermId 5
  
genTerm :: Int -> Gen Term
genTerm varRange
  = do
      tid <- genTermId varRange
      case tid of
        (AppId k) -> replicateM (arity k) arbitrary >>= return . App k
        LamId     -> genTerm varRange >>= return . Lam
        VarId n   -> return (Var n)
        LitId n   -> return (Lit n)
      
instance Arbitrary Term where
  arbitrary = genTerm 5
    
        
genName :: Gen String
genName = replicateM 5 $ elements ['a'..'z']
        
genLemma :: Gen (Name , Term)
genLemma 
  = do
    t1 <- arbitrary `suchThat` (lazyHeight 2)
    t2 <- arbitrary `suchThat` (lazyHeight 2)
    s  <- genName
    return $ (s, App "==" [t1 , t2])

lazyHeight :: Int -> Term -> Bool
lazyHeight 0 _ = True
lazyHeight n (Var _) = False
lazyHeight n (Lit _) = False
lazyHeight n (Lam t) = lazyHeight (n-1) t
lazyHeight n (App _ ts) = or $ map (lazyHeight $ n-1) ts
    
 
genTermFor :: Term -> Gen Term
genTermFor t@(App "==" [i , j])
  = do
    let vn = enumVars t
    ts <- replicateM (length vn) arbitrary
    let vnts = M.fromList $ zip vn ts
    let i'   = substVar vnts i
    let j'   = substVar vnts j
    ctx <- genTerm 0 `suchThat` (\ x -> enumVars x == [0] && lazyHeight 2 x)
    let ctx1 = substVar' 0 i' ctx
    let ctx2 = substVar' 0 j' ctx
    return $ App "==" [ctx1 , ctx2]
  where
    enumVars (Var n) = [n]
    enumVars (Lam t) = nub $ enumVars t
    enumVars (App _ ts) = nub $ concat $ map enumVars ts
    enumVars _       = []
    
    substVar dict (Var i)
      | (Just res) <- M.lookup i dict = res
      | otherwise                     = Var i
    substVar _    (Lit j) = Lit j
    substVar dict (Lam t) = Lam $ substVar dict t
    substVar dict (App n ts)
      = App n $ map (substVar dict) ts
      
    substVar' x y t = substVar (M.singleton x y) t
