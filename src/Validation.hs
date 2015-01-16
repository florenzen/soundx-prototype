module Validation where

import qualified Data.Set as S

import Syntax
import Unification
import Freshening

validate :: [Deriv] -> [InfRule] -> Deriv -> Bool
validate derivsAsm infRules deriv =
     validateByAsm derivsAsm deriv ||
     validateByRule derivsAsm infRules deriv ||
     validateByConstr deriv ||
     validateByFail deriv

validateByConstr :: Deriv -> Bool
validateByConstr (Deriv [] "Neq" (Neq (ELex lex1) (ELex lex2))) =
    lex1 /= lex2
validateByConstr _ = False

validateByFail :: Deriv -> Bool
validateByFail (Fail _) = True
validateByFail _ = False

validateByAsm :: [Deriv] -> Deriv -> Bool
validateByAsm [] deriv =
    False
validateByAsm (derivAsm:derivsAsm) deriv =
    case unifyJudg S.empty (concl derivAsm) (concl deriv) of
      Left msg -> validateByAsm derivsAsm deriv
      Right sub -> True

validateByRule :: [Deriv] -> [InfRule] -> Deriv -> Bool
validateByRule derivsAsm infRules (Deriv derivs name judg) =
    let res = findInfRule infRules name
    in case res of
         Just infRule ->
             let (subFresh, InfRule judgsIR nameIR judgIR) =
                     freshInfRule (varsDerivs derivsAsm `S.union`
                                   varsDeriv (Deriv derivs name judg))
                     infRule
                 varSet = varsJudgs (judgIR:judgsIR)
             in if length judgsIR == length derivs then
                    case unifyJudgs varSet (zip (judgIR:judgsIR)
                                            (judg : map concl derivs)) of
                      Left msg -> False -- error $ "wrong inst of " ++ name
                      Right sub -> all (validate derivsAsm infRules) derivs
                else
                    False
         Nothing -> False
validateByRule derivsAsm infRules (Fail judg) = False
