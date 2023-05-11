module Main (main) where
import Parser (astParse)
import Data.Either (fromRight)
import Desugar (desugar)
import SortDefs (sortDefs)
import TypeCheck
    ( prims, runInferSeq, union, TypeEnv(TypeEnv), schemeArity )
import Eval (evalName)
import qualified Data.Map as Map

main :: IO ()
main = do
    let code = "main = plusTwo 2 ; plusTwo = \\x -> plus x 2"
    let ast = fromRight (error "Parse fail") $ astParse code
    let (defs, conMap) = fromRight (error "Desugar fail") $ desugar ast
    let sortedDefs = sortDefs defs
    print $ fromRight (error "TypeCheck fail") $ runInferSeq (TypeEnv conMap `union` prims) sortedDefs
    -- There should be a modal check here
    print $ evalName "main" (Map.fromList defs, Map.map schemeArity conMap)
