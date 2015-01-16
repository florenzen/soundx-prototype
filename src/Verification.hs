module Verification where

-- import Debug.Trace

import           Rewrite
import           Syntax
import WFExt


soundExt :: Base -> Ext -> Either String ()
soundExt base ext@(Ext aritysX infRulesX univRRsX grdRRsX) = do
  mapM_ (classifyInfRule base ext) infRulesX

-- classifyInfRule :: Base -> Ext -> InfRule
--                 -> Either String InfRuleClass
-- classifyInfRule base ext infRule =
--     classifyInfRulePB base ext infRule
--     `catchError`
--     const (classifyInfRulePE base ext infRule)

-- classifyInfRulePB :: Base -> Ext -> InfRule
--                   -> Either String InfRuleClass
-- classifyInfRulePB base ext infRule = do
--   let arities = getBaseArities base
--       forms = getBaseForms base
--       infRules = getBaseInfRules base
--       Ext aritiesX infRulesX univRRsX grdRRsX = ext
--       InfRule judgsIR nameIR judgIR = infRule
--       (judgsIR',judgIR') = desugarInfRule univRRsX grdRRsX (judgsIR,judgIR)
--   when (judgIR' == judgIR)
--            (Left $ "Conclusion of rule cannot be desugared: " ++ nameIR)
--   when (not (all isRight (map (wfJudg arities forms) judgsIR')))
--            (Left $ "Is not a BU rule")
--   case deriveSub (map Asm judgsIR') infRules [judgIR'] S.empty of
--     Right (sub,[deriv']) ->
--         if validate (map Asm judgsIR') infRules deriv' then
--             Right PB
--         else
--             Left $ "Derivation for desugared conclusion from assumptions invalid"
--     Left msg -> Left $ nameIR ++ ": Desugared rule could not be derived: " ++
--                 msg ++ " from: " ++ show (map Asm judgsIR')

-- -- Implements S-TopDown
-- classifyInfRulePE :: Base -> Ext -> InfRule
--                   -> Either String InfRuleClass
-- classifyInfRulePE base ext infRule = do
--   let arities = getBaseArities base
--       forms = getBaseForms base
--       infRules = getBaseInfRules base
--       Ext aritiesX infRulesX univRRsX grdRRsX = ext
--       InfRule judgsIR nameIR judgIR = infRule
--       (judgsIR',judgIR') = desugarInfRule univRRsX grdRRsX (judgsIR,judgIR)
--   when (judgIR' == judgIR)
--            (Left $ "Conclusion of rule cannot be desugared: " ++ nameIR)
--   -- when (all isRight (map (wfJudg arities forms) judgsIR'))
--   --          (Left $ "Is not a TD rule: " ++ nameIR)
--   case deriveSub (map Asm judgsIR) infRules [judgIR'] S.empty of
--     Right (sub,[deriv']) ->
--         if validate (map Asm judgsIR) infRules deriv' then
--             case deriv' of
--               Asm _ -> Left $ "Desugared conclusion in assumptions"
--               Deriv _ name _ ->
--                   let unifyResults =
--                           map (\(judg1,judg2) ->
--                               unifyJudg (varsJudg judg1 `S.union` varsJudg judg2)
--                                judg1 judg2)
--                           (zip judgsIR (L.repeat judgIR'))
--                   in if all isLeft unifyResults then Right PE
--                      else Left $ "conclusion can be unified with assumption"
--         else
--             Left $ "Derivation for desugared conclusion from assumptions invalid"
--     Left msg -> Left $ nameIR ++ ": Desugared rule could not be derived: " ++ msg

-- soundInfRule :: Base -> Ext -> InfRule -> Either String ()
-- soundInfRule base ext infRule =
--     soundInfRuleBU base ext infRule
--     `catchError`
--     const (soundInfRuleTD base ext infRule)

-- -- Implements S-BottomUp
-- soundInfRuleBU :: Base -> Ext -> InfRule -> Either String ()
-- soundInfRuleBU base ext infRule = do
--   let arities = getBaseArities base
--       forms = getBaseForms base
--       infRules = getBaseInfRules base
--       Ext aritiesX infRulesX univRRsX grdRRsX = ext
--       InfRule judgsIR nameIR judgIR = infRule
--       (judgsIR',judgIR') = desugarInfRule univRRsX grdRRsX (judgsIR,judgIR)
--   when (judgIR' == judgIR)
--            (Left $ "Conclusion of rule cannot be desugared: " ++ nameIR)
--   when (not (all isRight (map (wfJudg arities forms) judgsIR')))
--            (Left $ "Is not a BU rule")
--   case derive (map Asm judgsIR') infRules judgIR' of
--     Right deriv' ->
--         if validate (map Asm judgsIR') infRules deriv' then
--             Right ()
--         else
--             Left $ "Derivation for desugared conclusion from assumptions invalid"
--     Left msg -> Left $ nameIR ++ ": Desugared rule could not be derived: " ++
--                 msg ++ " from: " ++ show (map Asm judgsIR')

-- -- Implements S-TopDown
-- soundInfRuleTD :: Base -> Ext -> InfRule -> Either String ()
-- soundInfRuleTD base ext infRule = do
--   let arities = getBaseArities base
--       forms = getBaseForms base
--       infRules = getBaseInfRules base
--       Ext aritiesX infRulesX univRRsX grdRRsX = ext
--       InfRule judgsIR nameIR judgIR = infRule
--       (judgsIR',judgIR') = desugarInfRule univRRsX grdRRsX (judgsIR,judgIR)
--   when (judgIR' == judgIR)
--            (Left $ "Conclusion of rule cannot be desugared: " ++ nameIR)
--   when (all isRight (map (wfJudg arities forms) judgsIR'))
--            (Left $ "Is not a TD rule: " ++ nameIR)
--   case derive (map Asm judgsIR) infRules judgIR' of
--     Right deriv' ->
--         if validate (map Asm judgsIR) infRules deriv' then
--             case deriv' of
--               Asm _ -> Left $ "Desugared conclusion in assumptions"
--               Deriv _ name _ ->
--                   let unifyResults =
--                           map (\(judg1,judg2) ->
--                               unifyJudg (varsJudg judg1 `S.union` varsJudg judg2)
--                                judg1 judg2)
--                           (zip judgsIR (L.repeat judgIR'))
--                   in if all isLeft unifyResults then Right ()
--                      else Left $ "conclusion can be unified with assumption"
--         else
--             Left $ "Derivation for desugared conclusion from assumptions invalid"
--     Left msg -> Left $ nameIR ++ ": Desugared rule could not be derived: " ++ msg

-- TODO: this function will be obsolete with modular extensions
verify :: Base -> [Ext] -> Ext -> Either String ()
verify base exts ext = do
    wfExt (foldl mergeBX base exts) ext
    soundExt (foldl mergeBX base exts) ext
