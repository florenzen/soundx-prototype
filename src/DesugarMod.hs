module DesugarMod where

import Syntax
import WFMod
import Rewrite


desugarMod :: [Intf] -> Base -> Mod -> Maybe Expr
desugarMod intfs base mod = do
  (intf,exts,deriv) <- wfMod intfs base mod
  deriv' <- desugar base exts deriv
  return (getJudgExpr (concl deriv') !! 0)
