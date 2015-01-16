module Verification where

-- import Debug.Trace

import qualified Data.Set as S
import Control.Monad
import Control.Monad.Error

import Validation
import Syntax
import Rewrite
import Derive
import WFBase
import Utils


soundExt :: Base -> Ext -> Either String ()
soundExt base ext@(Ext aritysX infRulesX univRRsX resRRsX) = do
  mapM_ (soundInfRule base ext) infRulesX

soundInfRule :: Base -> Ext -> InfRule -> Either String ()
soundInfRule base ext infRule =
    soundInfRuleBU base ext infRule
    `catchError`
    const (soundInfRuleTD base ext infRule)

-- Implements S-BottomUp
soundInfRuleBU :: Base -> Ext -> InfRule -> Either String ()
soundInfRuleBU base ext infRule = do
  let arities = getBaseArities base
      forms = getBaseForms base
      infRules = getBaseInfRules base
      Ext aritiesX infRulesX univRRsX resRRsX = ext
      InfRule judgsIR nameIR judgIR = infRule
      (judgsIR',judgIR') = desugarInfRule univRRsX resRRsX (judgsIR,judgIR)
  when (judgIR' == judgIR)
           (Left $ "Conclusion of rule cannot be desugared: " ++ nameIR)
  when (not (all isRight (map (wfJudg arities forms) judgsIR')))
           (Left $ "Is not a BU rule")
  case deriveSub (map Asm judgsIR') infRules [judgIR'] S.empty of
    Right (sub,[deriv']) ->
        if validate (map Asm judgsIR') infRules deriv' then
            Right ()
        else
            Left $ "Derivation for desugared conclusion from assumptions invalid"
    Left msg -> Left $ nameIR ++ ": Desugared rule could not be derived: " ++
                msg ++ " from: " ++ show (map Asm judgsIR')

-- Implements S-TopDown
soundInfRuleTD :: Base -> Ext -> InfRule -> Either String ()
soundInfRuleTD base ext infRule = do
  let arities = getBaseArities base
      forms = getBaseForms base
      infRules = getBaseInfRules base
      Ext aritiesX infRulesX univRRsX resRRsX = ext
      InfRule judgsIR nameIR judgIR = infRule
      (judgsIR',judgIR') = desugarInfRule univRRsX resRRsX (judgsIR,judgIR)
  when (judgIR' == judgIR)
           (Left $ "Conclusion of rule cannot be desugared: " ++ nameIR)
  when (all isRight (map (wfJudg arities forms) judgsIR'))
           (Left $ "Is not a TD rule: " ++ nameIR)
  case deriveSub (map Asm judgsIR) infRules [judgIR'] S.empty of
    Right (sub,[deriv']) ->
        if validate (map Asm judgsIR) infRules deriv' then
            Right ()
        else
            Left $ "Derivation for desugared conclusion from assumptions invalid"
    Left msg -> Left $ nameIR ++ ": Desugared rule could not be derived: " ++ msg

-- TODO: this function will be obsolete with modular extensions
verify :: Base -> [Ext] -> Ext -> Either String ()
verify base exts ext = do
    soundExt (foldl mergeBX base exts) ext
