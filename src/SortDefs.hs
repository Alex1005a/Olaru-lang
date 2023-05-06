{-# LANGUAGE TupleSections #-}
module SortDefs where

import qualified Data.Set as Set
import Expressions ( Name, Expr(..) )
import Data.Graph ( buildG, scc, Forest, Tree(..) )
import Data.Maybe (fromJust)
import Data.Tuple (swap)
import Data.Bifunctor (bimap, Bifunctor (..))

allCalls :: [Name] -> Expr a -> Set.Set Name
allCalls defs (NameExpr name)
    | name `elem` defs = Set.singleton name
    | otherwise = Set.empty
allCalls defs (LambdaExpr _ _ _ expr) = allCalls defs expr
allCalls _ (LitExpr _) = Set.empty
allCalls defs (ApplyExpr fun arg) = allCalls defs fun `Set.union` allCalls defs arg
allCalls defs (CaseExpr expr patterns) = allCalls defs expr `Set.union` foldr (Set.union . allCalls defs . snd) Set.empty patterns

treeToList :: Tree a -> [a]
treeToList (Node l subTrees) = l : concatMap treeToList subTrees

forestToList :: Forest a -> [[a]]
forestToList = map treeToList

sortFuns :: [Name] -> [(Name, Name)] -> [[Name]]
sortFuns funs calls =
  let indexFuns = zip funs [0..]
      indexCalls = map (bimap (fromJust . flip lookup indexFuns) (fromJust . flip lookup indexFuns)) calls
      forest = scc $ buildG (0, length indexFuns - 1) indexCalls
      lst = forestToList forest
      invertIdxFuns = map swap indexFuns in
  map (map (fromJust . flip lookup invertIdxFuns)) lst


sortDefs :: [(Name, Expr a)] -> [[(Name, Expr a)]]
sortDefs defs =
    let funs = map fst defs
        calls = concatMap (\(name, expr) -> map (name,) $ Set.toList (allCalls funs expr)) defs
        sortedDefs = sortFuns funs calls in
    map (map (\name -> (name, fromJust $ lookup name defs))) sortedDefs
