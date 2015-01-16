module Rewrite where

import Debug.Trace

import           Control.Applicative
import           Control.Monad
import           Control.Monad.Error
import qualified Data.List as L
import qualified Data.Map as M
import           Data.Maybe
import qualified Data.Set as S
import           Prelude hiding (repeat)
import           Data.Either.Utils

import           Derive
import           Freshening
import           Substitution
import           Syntax
import           Unification
import           Utils
import           WFBase
import           Validation

-- One step rewriting

rewriteExpr :: [UnivRR] -> Expr -> Maybe Expr
rewriteExpr univRRs expr =
    rewriteExprApply univRRs expr `mplus`
    rewriteExprTraverse univRRs expr

rewriteExprApply :: [UnivRR] -> Expr -> Maybe Expr
rewriteExprApply univRRs expr =
    transformLeftmost tryUnivRR univRRs
    where
      tryUnivRR univRR =
          let (subFresh, UnivRR expr1 expr2) = freshUnivRR (varsExpr expr) univRR
          in case unifyExpr (varsExpr expr1) expr1 expr of
               Left msg -> Nothing
               Right sub -> -- trace ("Expr1: " ++ show expr1 ++
                            --        "\nvars Expr1: " ++ show (varsExpr expr1) ++
                            --        "\nExpr: " ++ show expr ++
                            --        "\nSub " ++ show sub ++
                            --        "\nResult: " ++ show (applySubExpr sub expr2))
                            -- $
                            Just (applySubExpr sub expr2)

rewriteExprTraverse :: [UnivRR] -> Expr -> Maybe Expr
rewriteExprTraverse univRRs (ELex lex) = Nothing
rewriteExprTraverse univRRs (EVar var) = Nothing
rewriteExprTraverse univRRs (ECon name exprs) =
  pure (ECon name) <*> mapLeftmost (rewriteExpr univRRs) exprs

rewriteJudg :: [UnivRR] -> Judg -> Maybe Judg
rewriteJudg univRRs (Judg exprs name) =
  pure (flip Judg name) <*> mapLeftmost (rewriteExpr univRRs) exprs
rewriteJudg univRRs (Neq expr1 expr2) =
    pure Neq <*> rewriteExpr univRRs expr1 <*>
         rewriteExpr univRRs expr2

rewriteSub :: [UnivRR] -> Sub -> Maybe Sub
rewriteSub univRRs sub =
  let (vars,exprs) = unzip (M.toList sub)
  in pure (M.fromList . zip vars) <*> mapLeftmost (rewriteExpr univRRs) exprs

rewriteConcl :: [GrdRR] -> ([Judg], Judg) -> Maybe Judg
rewriteConcl grdRRs (judgs,judg) =
    transformLeftmost tryGrdRR grdRRs
    where
      tryGrdRR grdRR =
          let (subFresh, GrdRR judgs1 exprs1 expr exprs2 name expr2) =
                  freshGrdRR (varsJudgs (judg:judgs)) grdRR
              varSet = varsJudgs judgs1 `S.union`
                       varsExprs exprs1 `S.union`
                       varsExpr expr `S.union`
                       varsExprs exprs2 `S.union`
                       varsExpr expr2
          in case unifyJudgs varSet
                 (zip (Judg (exprs1 ++ expr:exprs2) name : judgs1)
                          (judg:judgs)) of
               Left msg -> Nothing
               Right sub ->
                   let Judg exprsIR nameIR = judg
                       (exprsIR1,exprIR:exprsIR2) =
                           L.splitAt (length exprs1) exprsIR
                       exprIR' = applySubExpr sub expr2
                   in Just $ Judg (exprsIR1++exprIR':exprsIR2) nameIR

rewriteInfRule :: [UnivRR] -> [GrdRR] -> ([Judg],Judg) -> Maybe ([Judg],Judg)
rewriteInfRule univRRs grdRRs (judgs,judg) =
    (do judg' <- rewriteJudg univRRs judg
        return (judgs,judg')) `mplus`
    (do judg' <- rewriteConcl grdRRs (judgs,judg)
        return (judgs,judg')) `mplus`
    (do judgs' <- mapLeftmost (rewriteJudg univRRs) judgs
        return (judgs',judg))

-- Desugaring (exhaustive rewriting)

desugarSub :: [UnivRR] -> Sub -> Sub
desugarSub univRRs sub = repeat (rewriteSub univRRs) sub

desugarInfRule :: [UnivRR] -> [GrdRR] -> ([Judg], Judg) -> ([Judg], Judg)
desugarInfRule univRRs grdRRs (judgs,judg) =
    repeat (rewriteInfRule univRRs grdRRs) (judgs,judg)

-- Original formulation with loop in ExtTD
-- desugarDeriv :: Base -> Ext -> Deriv -> Maybe Deriv
-- desugarDeriv base ext deriv@(Deriv derivs name judg) =
--     desugarDerivBase base ext deriv `mplus`
--     desugarDerivExtBU base ext deriv `mplus`
--     desugarDerivExtTD base ext deriv `mplus`
--     (error ("cannot desugar" ++ show (concl deriv)))

-- Only one topdown and one bottom up pass
-- desugarDeriv :: Base -> Ext -> Deriv -> Maybe Deriv
-- desugarDeriv base ext deriv =
--     let deriv' = topdown (rewriteDerivExtExt base ext) deriv
--         deriv'' = bottomup (\deriv -> rewriteDerivBase base ext deriv `mplus`
--                                       rewriteDerivExtBase base ext deriv) deriv'
--     in Just deriv''

-- Apply td desugarings on top-down descend and
-- bu desugarings on bottom-up ascend.
desugarDeriv :: Base -> Ext -> Deriv -> Maybe Deriv
desugarDeriv base ext deriv =
    Just $ downup rewriteTD rewriteBU deriv
    where
      rewriteBU deriv = fromJust (rewriteDerivBase base ext deriv `mplus`
                                  rewriteDerivExtBase base ext deriv)
                                  -- return deriv)
      rewriteTD deriv = fromJust (rewriteDerivExtExt base ext deriv `mplus`
                                  return deriv)


-- Implements D-Base
desugarDerivBase :: Base -> Ext -> Deriv -> Maybe Deriv
desugarDerivBase base ext deriv@(Deriv derivs name judg) = do
  let arities = getBaseArities base
      forms = getBaseForms base
      infRules = getBaseInfRules base
      Ext sdeclsX aritysX infRulesX univRRsX grdRRsX = ext
  infRule <- findInfRule infRules name
  let (subFresh, InfRule judgsIR nameIR judgIR) =
          freshInfRule (varsDeriv deriv) infRule
  derivs' <- mapM (desugarDeriv base ext) derivs
  sub1 <- case unifyJudgs (varsJudgs judgsIR)
               (zip judgsIR (map concl derivs')) of
            Right sub -> return sub
            Left msg -> error ("desugarDerivBase: forward step failed. STUCK." ++
                               "\n  Rule:        " ++ nameIR ++
                               "\n  Premises:    " ++ show judgsIR ++
                               "\n  Conclusions: " ++ show (map concl derivs') ++
                               "\n  Orig. Concl. " ++ show (map concl derivs) ++
                               "\n  Base rules   " ++ show (map getInfRuleName
                                                            (getBaseInfRules base)))
                        Nothing
  sub2 <- case (unifyJudg (varsJudg judgIR) judgIR judg) of
            Right sub -> Just sub
            Left msg -> error ("desugarDerivBase: could not calculate σ₂." ++
                               "MUST NOT HAPPEN" ++
                               "\n  Rule:                    " ++ nameIR ++
                               "\n  Rule's conclusion:       " ++ show judgIR ++
                               "\n  Derivation's conclusion: " ++ show judg)
  let sub21 = restrictSub sub2 (domSub sub2 `S.difference`
                                varsJudgs judgsIR)
      sub21' = desugarSub univRRsX sub21
      sub = sub21' `composeSub` sub1
  return (Deriv derivs' name (applySubJudg sub judgIR))

-- Implements D-ExtensionBU
desugarDerivExtBU :: Base -> Ext -> Deriv -> Maybe Deriv
desugarDerivExtBU base ext deriv@(Deriv derivs name judg) = do
  let sdecls = getBaseSortDecls base
      arities = getBaseArities base
      forms = getBaseForms base
      infRules = getBaseInfRules base
      Ext sdeclsX aritiesX infRulesX univRRsX grdRRsX = ext
  infRule <- findInfRule infRulesX name
  let (subFresh, infRule1@(InfRule judgsIR nameIR judgIR)) =
          freshInfRule (varsDeriv deriv) infRule
      (judgsIR',judgIR') = desugarInfRule univRRsX grdRRsX (judgsIR,judgIR)
  guard (all isRight (map (wfJudg sdecls arities forms) judgsIR'))
  derivs' <- mapM (desugarDeriv base ext) derivs
  sub1 <- case unifyJudgs (varsJudgs judgsIR')
                 (zip judgsIR' (map concl derivs')) of
            Right sub -> Just sub
            Left msg -> error ("desugarDerivExtBU: forward step failed. STUCK." ++
                               "\n  Rule:        " ++ nameIR ++
                               "\n  Premises:    " ++ show judgsIR' ++
                               "\n  Conclusions: " ++ show (map concl derivs'))
                        Nothing
  sub2 <- case (unifyJudg (varsJudg judgIR) judgIR judg) of
            Right sub -> Just sub
            Left msg -> error ("desugarDerivExtBU: could not calculate σ₂. " ++
                               "MUST NOT HAPPEN" ++
                               "\n  Rule:                    " ++ nameIR ++
                               "\n  Rule's conclusion:       " ++ show judgIR ++
                               "\n  Derivation's conclusion: " ++ show judg)
  let sub21 = restrictSub sub2 (domSub sub2 `S.difference`
                                varsJudgs judgsIR')
      sub21' = desugarSub univRRsX sub21
      judgIR'' = applySubJudg (sub1 `composeSub` sub21') judgIR'
      deriveResult = derive derivs' infRules judgIR''
  case deriveResult of
    Right deriv' -> return deriv'
    Left msg -> error ("desugarDerivExtBU: resolution failed. MUST NOT HAPPEN" ++
                       "\n  Conclusion to derive:       " ++ show judgIR'' ++
                       "\n  Conclusions of assumptions: " ++
                       show (map concl derivs'))

-- Implements D-ExtensionTD
desugarDerivExtTD :: Base -> Ext -> Deriv -> Maybe Deriv
desugarDerivExtTD base ext deriv@(Deriv derivs name judg) = do
  let sdecls = getBaseSortDecls base
      arities = getBaseArities base
      forms = getBaseForms base
      infRules = getBaseInfRules base
      Ext sdeclsX aritiesX infRulesX univRRsX grdRRsX = ext
  infRule <- findInfRule infRulesX name
  let (subFresh, infRule1@(InfRule judgsIR nameIR judgIR)) =
          freshInfRule (varsDeriv deriv) infRule
      (judgsIR',judgIR') = desugarInfRule univRRsX grdRRsX (judgsIR,judgIR)
  guard (not (all isRight (map (wfJudg sdecls arities forms) judgsIR')))
  sub <- case unifyJudgs (varsJudgs (judgIR:judgsIR))
                (zip (judgIR:judgsIR) (judg : map concl derivs)) of
           Right sub -> Just sub
           Left msg -> error ("desugarDerivExtTD: could not calculate σ." ++
                              "\n  Rule:        " ++ nameIR ++
                              "\n  Premises:    " ++ show judgsIR ++
                              "\n  Conlcusions: " ++ show (map concl derivs))
  let judgIR'' = applySubJudg sub judgIR'
      deriveResult = derive derivs (infRules++infRulesX) judgIR''
  case deriveResult of
    Right deriv' -> desugarDeriv base ext deriv'
    Left msg -> error ("desugarDerivExtTD: resolution failed." ++
                       "\n  Conclusion to derive:       " ++ show judgIR'' ++
                       "\n  Conclusions of assumptions: " ++
                       show (map concl derivs))

rewriteDerivBase :: Base -> Ext -> Deriv -> Maybe Deriv
rewriteDerivBase base ext deriv@(Deriv [] _ (Neq _ _)) =
    return deriv -- There can only be lexical expressions
                 -- Neq which cannot be desugared
                 -- They are excluded by the wf conditions
rewriteDerivBase base ext deriv@(Deriv derivs name judg) = do
  let arities = getBaseArities base
      forms = getBaseForms base
      infRules = getBaseInfRules base
      Ext sdeclsX aritysX infRulesX univRRsX grdRRsX = ext
  infRule <- findInfRule infRules name
  let (subFresh, InfRule judgsIR nameIR judgIR) =
          freshInfRule (varsDeriv deriv) infRule
  sub1 <- case unifyJudgs (varsJudgs judgsIR)
               (zip judgsIR (map concl derivs)) of
            Right sub -> return sub
            Left msg -> error ("desugarDerivBase: forward step failed. STUCK." ++
                               "\n  Rule:        " ++ nameIR ++
                               "\n  Premises:    " ++ show judgsIR ++
                               "\n  Conclusions: " ++ show (map concl derivs) ++
                               "\n  Base rules   " ++ show (map getInfRuleName
                                                            (getBaseInfRules base)))
                        Nothing
  sub2 <- case (unifyJudg (varsJudg judgIR) judgIR judg) of
            Right sub -> Just sub
            Left msg -> error ("desugarDerivBase: could not calculate σ₂." ++
                               "MUST NOT HAPPEN" ++
                               "\n  Rule:                    " ++ nameIR ++
                               "\n  Rule's conclusion:       " ++ show judgIR ++
                               "\n  Derivation's conclusion: " ++ show judg)
  let sub21 = restrictSub sub2 (domSub sub2 `S.difference`
                                varsJudgs judgsIR)
      sub21' = desugarSub univRRsX sub21
      sub = sub21' `composeSub` sub1
  return (Deriv derivs name (applySubJudg sub judgIR))

rewriteDerivExtBase :: Base -> Ext -> Deriv -> Maybe Deriv
rewriteDerivExtBase base ext deriv@(Deriv derivs name judg) = do
  let sdecls = getBaseSortDecls base
      arities = getBaseArities base
      forms = getBaseForms base
      infRules = getBaseInfRules base
      Ext sdeclsX aritiesX infRulesX univRRsX grdRRsX = ext
  infRule <- findInfRule infRulesX name
  let (subFresh, infRule1@(InfRule judgsIR nameIR judgIR)) =
          freshInfRule (varsDeriv deriv) infRule
      (judgsIR',judgIR') = desugarInfRule univRRsX grdRRsX (judgsIR,judgIR)
  -- guard (all isRight (map (wfJudg arities forms) judgsIR'))
  -- derivs' <- mapM (desugarDeriv base ext) derivs
  sub1 <- case unifyJudgs (varsJudgs judgsIR')
                 (zip judgsIR' (map concl derivs)) of
            Right sub -> Just sub
            Left msg -> error ("desugarDerivExtBU: forward step failed. STUCK." ++
                               "\n  Rule:        " ++ nameIR ++
                               "\n  Premises:    " ++ show judgsIR' ++
                               "\n  Conclusions: " ++ show (map concl derivs))
                        Nothing
  sub2 <- case (unifyJudg (varsJudg judgIR) judgIR judg) of
            Right sub -> Just sub
            Left msg -> error ("desugarDerivExtBU: could not calculate σ₂. " ++
                               "MUST NOT HAPPEN" ++
                               "\n  Rule:                    " ++ nameIR ++
                               "\n  Rule's conclusion:       " ++ show judgIR ++
                               "\n  Derivation's conclusion: " ++ show judg)
  let sub21 = restrictSub sub2 (domSub sub2 `S.difference`
                                varsJudgs judgsIR')
      sub21' = desugarSub univRRsX sub21
      judgIR'' = applySubJudg (sub1 `composeSub` sub21') judgIR'
      deriveResult = derive derivs infRules judgIR''
  case deriveResult of
    Right deriv' -> return deriv'
    Left msg -> error ("desugarDerivExtBU: resolution failed. MUST NOT HAPPEN" ++
                       "\n  Conclusion to derive:       " ++ show judgIR'' ++
                       "\n  Conclusions of assumptions: " ++
                       show (map concl derivs))


rewriteDerivExtExt :: Base -> Ext -> Deriv -> Maybe Deriv
rewriteDerivExtExt base ext deriv@(Deriv derivs name judg) = do
  let sdecls = getBaseSortDecls base
      arities = getBaseArities base
      forms = getBaseForms base
      infRules = getBaseInfRules base
      Ext sdeclsX aritiesX infRulesX univRRsX grdRRsX = ext
  infRule <- findInfRule infRulesX name
  let (subFresh, infRule1@(InfRule judgsIR nameIR judgIR)) =
          freshInfRule (varsDeriv deriv) infRule
      (judgsIR',judgIR') = desugarInfRule univRRsX grdRRsX (judgsIR,judgIR)
  --guard (not (all isRight (map (wfJudg arities forms) judgsIR')))
  guard (fromRight (classifyInfRule base ext infRule) == PE)
  sub <- case unifyJudgs (varsJudgs (judgIR:judgsIR))
                (zip (judgIR:judgsIR) (judg : map concl derivs)) of
           Right sub -> Just sub
           Left msg -> error ("desugarDerivExtTD: could not calculate σ. " ++
                              "MUST NOT HAPPEN" ++
                              "\n  Rule:        " ++ nameIR ++
                              "\n  Premises:    " ++ show judgsIR ++
                              "\n  Conlcusions: " ++ show (map concl derivs))
  let judgIR'' = applySubJudg sub judgIR'
      deriveResult = derive derivs (infRules++infRulesX) judgIR''
  case deriveResult of
    Right deriv' -> return deriv'
    -- desugarDeriv base ext deriv'
    Left _ -> error ("desugarDerivExtTD: resolution failed. MUST NOT HAPPEN" ++
                       "\n  Conclusion to derive:       " ++ show judgIR'' ++
                       "\n  Conclusions of assumptions: " ++
                       show (map concl derivs))


-- Rewrite strategies (from Stratego tutorial)

-- downup(s1, s2) = s1; all(downup(s1, s2)); s2
-- downup(s) = s; all(downup(s)); s
downup :: (Deriv -> Deriv) -> (Deriv -> Deriv) -> Deriv -> Deriv
downup td bu deriv@(Deriv derivs name judg) =
    let deriv'@(Deriv derivs' name' judg') = td deriv
        derivs'' = map (downup td bu) derivs'
        deriv'' = bu (Deriv derivs'' name' judg')
    in deriv''

topdown :: (Deriv -> Maybe Deriv) -> Deriv -> Deriv
topdown f deriv@(Deriv derivs name judg) =
    case f deriv of
      Nothing ->
        let derivs' = map (topdown f) derivs
        in  (Deriv derivs' name judg)
      Just deriv'@(Deriv derivs' name' judg') ->
          let derivs'' = map (topdown f) derivs'
          in (Deriv derivs'' name' judg')

bottomup :: (Deriv -> Maybe Deriv) -> Deriv -> Deriv
bottomup f deriv@(Deriv derivs name judg) =
    let derivs' = map (bottomup f) derivs
    in case f (Deriv derivs' name judg) of
         Nothing -> Deriv derivs' name judg
         Just deriv'' -> deriv''



desugar :: Base -> [Ext] -> Deriv -> Deriv
desugar base [] deriv = deriv
desugar base (ext:exts) deriv =
  let base1 = foldl mergeBX base exts
      deriv' = fromJust $ desugarDeriv base1 ext deriv
  in desugar base exts deriv'

desugarMod :: Base -> [Ext] -> Deriv -> Expr
desugarMod base [] deriv =
    let Judg [exprRep,exprMod,exprSig] name = concl deriv
    in exprMod
desugarMod base exts deriv =
    let (exts1,ext) = (init exts, last exts)
        baseX = foldl mergeBX base exts1
        deriv' = fromJust $ desugarDeriv baseX ext deriv
    in desugarMod base exts1 deriv'




-- TODO: copied from Verification to avoid
-- cyclic dependency. Must be refactored
classifyInfRule :: Base -> Ext -> InfRule
                -> Either String InfRuleClass
classifyInfRule base ext infRule =
    classifyInfRulePB base ext infRule
    `catchError`
    (\msg1 -> (classifyInfRulePE base ext infRule)
             `catchError`
             (\msg2 ->
                  (Left ("The rule " ++ (getInfRuleName infRule) ++
                         "cannot be verified:\n" ++
                         msg1 ++ "\n" ++ msg2))))

classifyInfRulePB :: Base -> Ext -> InfRule
                  -> Either String InfRuleClass
classifyInfRulePB base ext infRule = do
  let sdecls = getBaseSortDecls base
      arities = getBaseArities base
      forms = getBaseForms base
      infRules = getBaseInfRules base
      Ext sdelcsX aritiesX infRulesX univRRsX grdRRsX = ext
      InfRule judgsIR nameIR judgIR = infRule
      (judgsIR',judgIR') = desugarInfRule univRRsX grdRRsX (judgsIR,judgIR)
  when (not (all isRight (map (wfJudg sdecls arities forms) judgsIR')))
           (Left $ "cannot be classified as B rule")
  case derive (map Asm judgsIR') infRules judgIR' of
    Right deriv' ->
        if validate (map Asm judgsIR') infRules deriv' then
            Right PB
        else
            error "Derivation for desugared conclusion from assumptions invalid"
    Left msg -> Left $ nameIR ++
                ": Desugared rule could not be derived: " ++
                msg ++ " from: " ++ show (map Asm judgsIR')

classifyInfRulePE :: Base -> Ext -> InfRule
                  -> Either String InfRuleClass
classifyInfRulePE base ext infRule = do
  let arities = getBaseArities base
      forms = getBaseForms base
      infRules = getBaseInfRules base
      Ext sdeclsX aritiesX infRulesX univRRsX grdRRsX = ext
      InfRule judgsIR nameIR judgIR = infRule
      (judgsIR',judgIR') = desugarInfRule univRRsX grdRRsX
                           (judgsIR,judgIR)
  case derive (map Asm judgsIR) (infRules++infRulesX) judgIR' of
    Right deriv' ->
        if validate (map Asm judgsIR) (infRules++infRulesX) deriv' then
            case deriv' of
              Asm _ -> Left $ "Desugared conclusion in assumptions"
              Deriv _ name _ ->
                  case findInfRule infRules name of
                    Nothing -> Left $ "Last node must be a base rule instantiation"
                    Just _ -> Right PE
        else
            error "Derivation for desugared conclusion from assumptions invalid"
    Left msg -> Left $ nameIR ++
                ": Desugared rule could not be derived: " ++ msg
