module WFExt where

-- import Debug.Trace

import Control.Monad
import Control.Monad.Error
import qualified Data.Set as S


import WFBase
import Syntax


wfExt :: Base -> Ext -> Either String ()
wfExt base (Ext aritiesX infRulesX univRRs grdRRs) = do
  let arities = getBaseArities base
      forms = getBaseForms base
      infRules = getBaseInfRules base
  wfArities (arities++aritiesX)
  wfInfRules (arities++aritiesX) forms (infRules++infRulesX)
  mapM_ (wfGrdRR (arities++aritiesX) forms) grdRRs
  mapM_ (wfUnivRR (arities++aritiesX)) univRRs

-- Implements W-Universal
wfUnivRR :: [Arity] -> UnivRR -> Either String ()
wfUnivRR arities (UnivRR (EVar var) expr') =
    throwError "lhs cannot be a variable"
wfUnivRR arities (UnivRR expr@(ECon name exprs) expr') = do
  nameS  <- wfExpr arities (ECon name exprs)
  nameS' <- wfExpr arities expr'
  unless (nameS == nameS')
             (throwError "sorts of lhs and rhs do not match")
  unless (varsExpr expr' `S.isSubsetOf` varsExpr expr)
             (throwError "variables of rhs must be subset of lhs variables")
  -- [Note 1]
  -- unless (isJust (findArity aritiesX name))
  --            (throwError $ "constructor on lhs not from extension: " ++ name)

-- Implements W-Guarded
wfGrdRR :: [Arity] -> [Form] -> GrdRR -> Either String ()
wfGrdRR arities forms
            (GrdRR judgs exprs1 (EVar var) exprs2 name1 expr') =
                throwError "lhs cannot be a variable"
wfGrdRR arities forms
        (GrdRR judgs exprs1 expr@(ECon name exprs) exprs2 name1 expr') = do
  mapM_ (wfJudg arities forms) judgs
  wfJudg arities forms
             (Judg (exprs1++[ECon name exprs]++exprs2) name1)
  nameS <- wfExpr arities (ECon name exprs)
  nameS' <- wfExpr arities expr'
  unless (nameS == nameS')
             (throwError "sorts of lhs and rhs do not match")
  let varSetLhs = varsJudgs judgs `S.union` varsExprs exprs1
                  `S.union` varsExpr expr `S.union` varsExprs exprs2
  unless (varsExpr expr' `S.isSubsetOf` varSetLhs)
             (throwError "variables of rhs must be subset of lhs variables")
  -- [Note 1]
  -- unless (isJust (findArity aritiesX name))
  --            (throwError $ "constructor on lhs not from extension: " ++ name)

-- ~~~ Note 1 ~~~
-- This check is not necessary since a desugaring that redefines a base language
-- expression is never applied. See testcases test30--test33 and extensions
-- extRedefPlusU and extRedefPlusR.
