module WFExt where

-- import Debug.Trace

import Control.Monad
import Control.Monad.Error
import qualified Data.Set as S


import WFBase
import Syntax


wfExt :: Base -> Ext -> Either String ()
wfExt base (Ext sdeclsX aritiesX infRulesX univRRs grdRRs) = do
  let sdecls = getBaseSortDecls base
      arities = getBaseArities base
      forms = getBaseForms base
      infRules = getBaseInfRules base
  wfSortDecls (sdecls++sdeclsX)
  wfArities (sdecls++sdeclsX) (arities++aritiesX)
  wfInfRules (sdecls++sdeclsX) (arities++aritiesX) forms (infRules++infRulesX)
  mapM_ (wfGrdRR (sdecls++sdeclsX) (arities++aritiesX) forms) grdRRs
  mapM_ (wfUnivRR (sdecls++sdeclsX) (arities++aritiesX)) univRRs

-- Implements W-Universal
wfUnivRR :: [SortDecl] -> [Arity] -> UnivRR -> Either String ()
wfUnivRR sdecls arities (UnivRR (ELex lex) expr') =
    throwError "lhs cannot be a lexical constant"
wfUnivRR sdecls arities (UnivRR (EVar var) expr') =
    throwError "lhs cannot be a variable"
wfUnivRR sdecls arities (UnivRR expr@(ECon name exprs) expr') = do
  nameS  <- wfExpr sdecls arities (ECon name exprs)
  nameS' <- wfExpr sdecls arities expr'
  unless (nameS == nameS')
             (throwError "sorts of lhs and rhs do not match")
  unless (varsExpr expr' `S.isSubsetOf` varsExpr expr)
             (throwError "variables of rhs must be subset of lhs variables")
  -- [Note 1]
  -- unless (isJust (findArity aritiesX name))
  --            (throwError $ "constructor on lhs not from extension: " ++ name)

-- Implements W-Guarded
wfGrdRR :: [SortDecl] -> [Arity] -> [Form] -> GrdRR -> Either String ()
wfGrdRR sdecls arities forms
            (GrdRR judgs exprs1 (EVar var) exprs2 name1 expr') =
                throwError "lhs cannot be a variable"
wfGrdRR sdecls arities forms
        (GrdRR judgs exprs1 expr@(ECon name exprs) exprs2 name1 expr') = do
  mapM_ (wfJudg sdecls arities forms) judgs
  wfJudg sdecls arities forms
             (Judg (exprs1++[ECon name exprs]++exprs2) name1)
  nameS <- wfExpr sdecls arities (ECon name exprs)
  nameS' <- wfExpr sdecls arities expr'
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
