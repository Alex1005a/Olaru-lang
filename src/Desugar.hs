module Desugar where
import qualified Parser as P
import Expressions (Expr (NameExpr, LambdaExpr, LitExpr, ApplyExpr, CaseExpr))
import Algebra (Modality(Unrestricted))
import Data.Foldable (foldl')
import Data.Bifunctor (second)

desugarExpr :: P.SugarExpr -> Expr ()
desugarExpr (P.NameExpr name) = NameExpr name
desugarExpr (P.LitExpr litt) = LitExpr litt
desugarExpr (P.LambdaExpr args sexpr) = do
  let expr = desugarExpr sexpr in
    foldr (\n -> LambdaExpr n () Unrestricted) expr args
desugarExpr (P.ApplyExpr fun args) = do
  let funExpr = desugarExpr fun
      argExprs = desugarExpr <$> args in
    foldl' ApplyExpr funExpr argExprs
desugarExpr (P.CaseExpr sexpr patterns) =
  let expr = desugarExpr sexpr
      desugaredPats = second desugarExpr <$> patterns in
    CaseExpr expr desugaredPats