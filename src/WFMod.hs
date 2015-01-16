module WFMod where

-- import Debug.Trace
import Control.Monad
import Control.Monad.Error
import qualified Data.List as L

import Derive
import Freshening
import Syntax
import Verification
import WFBase
import WFExt


-- Import statements are not extensible
-- since extension do not contain the necessary
-- additions to the module system definitions

intfMod :: [Intf] -> Base -> Mod -> Either String Intf
intfMod intfs base mod = do
    (intf,exts,deriv) <- wfMod intfs base mod
    return intf

wfMod :: [Intf] -> Base -> Mod -> Either String (Intf,[Ext],Deriv)
wfMod intfs base mod = do
  let sdecls = getBaseSortDecls base
      arities = getBaseArities base

  -- Module system definition from base system
  let modCon = getBaseModCon base
      modIdSort = getBaseModIdSort base
      impsSort = getBaseImpsSort base
      impsConNil = getBaseImpsConNil base
      impsConCons = getBaseImpsConCons base
      impCons = getBaseImpCons base
      sigSort = getBaseSigSort base
      sigJudg = getBaseSigJudg base
      sigRepNil = getBaseSigRepConNil base
      sigRepCons = getBaseSigRepConCons base

  -- Decompose module
  let expr = getModExpr mod
      ext = getModExt mod

  -- expr must be build by module constructor, module identifier must be of
  -- correct sort, and import list must be well-formed.
  -- We cannot simply check the entire module for well-formedness since
  -- the body possibly contains constructors from imported extensions
  -- and we cannot process the imports before we have ensured their
  -- well-formedness.
  unless (getEConName expr == modCon)
             (throwError "not the module constructor")
  unless (length (getEConExprs expr) > 1)
           (throwError "module constructor applied to too few arguments")

  -- Module identifier
  let modId = getEConExprs expr !! 0
  nameS <- wfExpr sdecls arities modId
  unless (nameS == modIdSort)
         (throwError "module identifier of wrong sort")
  -- Import list
  let imps = getEConExprs expr !! 1
  nameS <- wfExpr sdecls arities imps
  unless (nameS == impsSort)
         (throwError "import list not well-formed")

  -- Get identifiers of imported modules
  modIds <- findModIdsImp impsConNil impsConCons impCons imps

  -- Build list of imported extensions
  intfsImp <- findIntfs intfs modIds
  let extsImp = L.nub (concatMap getIntfExts intfsImp)
                -- L.nub keeps left-most occurence of an extension

  -- Is composition of imported extensions well-formed?
  wfExts base extsImp
  let baseX = foldl mergeBX base extsImp

  -- Is extension defined in this module well-formed and sound
  -- with respect to base system and imported extensions?
  wfExt baseX ext
  soundExt baseX ext

  -- Build module signature:
  -- 1. Build signature repository
  -- 2. Build signature judgment to derive
  -- 3. Derive signature judgment
  -- 4. Extract signature from derived substitution
  let varSig = pickFreshVar (varsExpr expr) (Var "sig" sigSort)
      sigRep = foldr (\intf rep ->
                       ECon sigRepCons [getIntfId intf,getIntfExpr intf,rep])
               (ECon sigRepNil []) intfs
      judgSig = Judg [sigRep, expr, EVar varSig] sigJudg

  deriv <- derive [] (getBaseInfRules baseX) judgSig

  let Judg [_,_,exprSig] _ = concl deriv
                             --applySubExpr sub (EVar varSig)

  -- Interface: signature and imported plus defined extensions
  return (Intf modId exprSig (extsImp++[ext]), extsImp, deriv)

buildDerivation1 :: [Deriv] -> [InfRule] -> Judg
                 -> Either String Deriv
buildDerivation1 derivsAsm infRules judg =
    case buildDerivation derivsAsm infRules judg of
      Left derivs -> Left (show derivs)
      Right deriv -> Right deriv

findModIdsImp :: Name -> Name -> [Name] -> Expr -> Either String [Expr]
findModIdsImp impsConNil impsConCons impCons (EVar var) =
    throwError "metavariable in import list"
findModIdsImp impsConNil impsConCons impCons (ECon name exprs) = do
  if name == impsConNil then
      return []
  else
      if name == impsConCons then do
          let expr1 = exprs!!0
              expr2 = exprs!!1
          modId <- findModIdImp impCons expr1
          modIds <- findModIdsImp impsConNil impsConCons impCons expr2
          return (modId:modIds)
      else
          throwError "wrong constructor in import list"

findModIdImp :: [Name] -> Expr -> Either String Expr
findModIdImp names (EVar var) =
    throwError "metavariable in import list"
findModIdImp names (ECon name exprs) =
    if name `elem` names then
        return (exprs!!0)
    else
        throwError "wrong import constructor in import list"

-- wfSoundExt :: Base -> Ext -> Either String ()
-- wfSoundExt base ext = do
--   wfExt base ext
  -- soundExt base ext

wfExts :: Base -> [Ext] -> Either String ()
wfExts base exts =
    foldM_ (\base ext -> do
             wfExt base ext
             return (mergeBX base ext)) base exts

findIntfs :: [Intf] -> [Expr] -> Either String [Intf]
findIntfs intfs exprs = mapM (findIntf intfs) exprs

findIntf :: [Intf] -> Expr -> Either String Intf
findIntf intfs expr =
    case L.find ((expr ==) . getIntfId) intfs of
      Nothing -> throwError ("interface not found: " ++ show expr)
      Just intf -> return intf
