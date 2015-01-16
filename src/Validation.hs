module Validation where

-- import Debug.Trace
import Data.Maybe
import qualified Data.Set as S

import Syntax
import Unification
import Freshening

validate :: [Deriv] -> [InfRule] -> Deriv -> Bool
validate derivsAsm infRules deriv =
     validateByAsm derivsAsm deriv ||
     validateByRule derivsAsm infRules deriv

validateByAsm :: [Deriv] -> Deriv -> Bool
validateByAsm [] deriv =
    False
validateByAsm (derivAsm:derivsAsm) deriv =
    case unifyJudg S.empty (concl derivAsm) (concl deriv) of
      Left msg -> validateByAsm derivsAsm deriv
      Right sub -> True

validateByRule :: [Deriv] -> [InfRule] -> Deriv -> Bool
validateByRule derivsAsm infRules (Deriv derivs name judg) =
    let infRule = fromJust (findInfRule infRules name)
        (subFresh, InfRule judgsIR nameIR judgIR) =
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
