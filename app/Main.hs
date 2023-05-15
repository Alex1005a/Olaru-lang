module Main (main) where
import Parser (astParse)
import Data.Either (fromRight)
import Desugar (desugar)
import SortDefs (sortDefs)
import TypeCheck
    ( prims, runInferSeq, union, TypeEnv(TypeEnv), schemeArity )
import Eval (evalName)
import qualified Data.Map as Map
import ModalCheck (runMcheck)

main :: IO ()
main = do
    let code = "main = plusTwo 2 ; plusTwo = \\x -> plus x 2"
    let ast = fromRight (error "Parse fail") $ astParse code
    let (defs, conMap) = fromRight (error "Desugar fail") $ desugar ast
    let sortedDefs = sortDefs defs
    let tyCheckResult = fromRight (error "TypeCheck fail") $ runInferSeq (TypeEnv conMap `union` prims) sortedDefs
    print $ fromRight (error "ModalCheck fail") $ runMcheck tyCheckResult
    print $ evalName "main" (Map.fromList $ (\(n, e, _) -> (n, e)) <$> tyCheckResult) (Map.map schemeArity conMap)
