module WFExt where

-- import Debug.Trace

import Control.Monad
import Control.Monad.Error

import WFBase
import Syntax


wfExt :: Base -> Ext -> Either String ()
wfExt base (Ext aritiesX infRulesX univRRs resRRs) = do
  let arities = getBaseArities base
      forms = getBaseForms base
      infRules = getBaseInfRules base
  wfArities arities aritiesX
  wfInfRules (arities++aritiesX) forms infRules infRulesX
  mapM_ (wfResRR aritiesX arities forms) resRRs
  mapM_ (wfUnivRR aritiesX arities) univRRs

-- Implements W-Universal
wfUnivRR :: [Arity] -> [Arity] -> UnivRR -> Either String ()
wfUnivRR aritiesX arities (UnivRR (EVar var) expr') =
    throwError "lhs cannot be a variable"
wfUnivRR aritiesX arities (UnivRR (ECon name exprs) expr') = do
  nameS  <- wfExpr (aritiesX++arities) (ECon name exprs)
  nameS' <- wfExpr (aritiesX++arities) expr'
  unless (nameS == nameS')
             (throwError "sorts of lhs and rhs do not match")
  -- [Note 1]
  -- unless (isJust (findArity aritiesX name))
  --            (throwError $ "constructor on lhs not from extension: " ++ name)

-- Implements W-Restricted
wfResRR :: [Arity] -> [Arity] -> [Form] -> ResRR -> Either String ()
wfResRR aritiesX arities forms
            (ResRR judgs exprs1 (EVar var) exprs2 name1 expr') =
                throwError "lhs cannot be a variable"
wfResRR aritiesX arities forms
        (ResRR judgs exprs1 (ECon name exprs) exprs2 name1 expr') = do
  mapM_ (wfJudg (aritiesX++arities) forms) judgs
  wfJudg (aritiesX++arities) forms
             (Judg (exprs1++[ECon name exprs]++exprs2) name1)
  nameS <- wfExpr (aritiesX++arities) (ECon name exprs)
  nameS' <- wfExpr (aritiesX++arities) expr'
  unless (nameS == nameS')
             (throwError "sorts of lhs and rhs do not match")
  -- [Note 1]
  -- unless (isJust (findArity aritiesX name))
  --            (throwError $ "constructor on lhs not from extension: " ++ name)

-- ~~~ Note 1 ~~~
-- This check is not necessary since a desugaring that redefines a base language
-- expression is never applied. See testcases test30--test33 and extensions
-- extRedefPlusU and extRedefPlusR.
