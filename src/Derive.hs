module Derive where

-- import Debug.Trace

import Control.Monad.Error
import qualified Data.Set as S

import Syntax
import Substitution
import Unification
import Freshening

derive :: [Deriv] -> [InfRule] -> Judg -> Either String Deriv
derive derivsAsm infRules judg =
    let varsAsm = varsDerivs derivsAsm
        varsGoal = varsJudg judg
        varsUnify = varsGoal `S.difference` varsAsm
    in case deriveMany derivsAsm infRules [judg] varsUnify of
         Left msg -> Left msg
         Right [deriv] -> Right deriv

deriveMany :: [Deriv] -> [InfRule] -> [Judg] -> S.Set Var
       -> Either String [Deriv]
deriveMany derivsAsm infRules judgs varSet = do
  (sub,derivs) <- deriveSub derivsAsm infRules judgs varSet
  return derivs

deriveSub :: [Deriv] -> [InfRule] -> [Judg] -> S.Set Var
          -> Either String (Sub,[Deriv])
deriveSub derivsAsm infRules [] varSet = return (emptySub,[])
deriveSub derivsAsm infRules (judg:judgs) varSet =
    deriveSubByAsm derivsAsm derivsAsm infRules
                   (judg:judgs) varSet
    `catchError`
    (\msg ->
         deriveSubByRule derivsAsm infRules infRules
                             (judg:judgs) varSet)

deriveSubByRule :: [Deriv] -> [InfRule] -> [InfRule] -> [Judg] -> S.Set Var
                -> Either String (Sub,[Deriv])
deriveSubByRule derivsAsm infRulistAll [] (judg:judgs) varSet =
    Left $ "Could not derive " ++ show judg ++ " and\n" ++ show judgs ++
         "\nfrom assumptions: " ++ show derivsAsm
deriveSubByRule derivsAsm infRulesAll (infRule:infRules)
                    (judg:judgs) varSet =
    (do let varSetJudgsDerivs = (varsDerivs derivsAsm `S.union`
                                 varsJudgs (judg:judgs))
            (subFresh, InfRule judgsP nameIR judgC) =
               freshInfRule (varSetJudgsDerivs `S.union` varSet)
               infRule
            varSetFresh = S.map getEVarVar (ranSub subFresh)
            varSet1 = varSet `S.union` varSetFresh
        subMgu <- unifyJudg varSet1 judg judgC
        (sub,derivs) <- deriveSub derivsAsm infRulesAll
                           (applySubJudgs subMgu (judgsP++judgs)) varSet1
        let (derivsP,derivsOther) = splitAt (length judgsP) derivs
            sub1 = sub `composeSub` subMgu
        return (sub1,
                Deriv derivsP nameIR (applySubJudg sub1 judg) :
                derivsOther))
    `catchError`
    (\msg -> deriveSubByRule derivsAsm infRulesAll
             infRules (judg:judgs) varSet)

deriveSubByAsm :: [Deriv] -> [Deriv] -> [InfRule] -> [Judg] -> S.Set Var
               -> Either String (Sub,[Deriv])
deriveSubByAsm derivsAll [] infRules (judg:judgs) varSet =
    Left $ "Could not derive " ++ show judg ++ " by assumption"
deriveSubByAsm derivsAll (deriv:derivs) infRules (judg:judgs) varSet =
    (do subMgu <- unifyJudg varSet judg (concl deriv)
        (sub,derivs) <- deriveSub derivsAll infRules
                           (applySubJudgs subMgu judgs) varSet
        let sub1 = sub `composeSub` subMgu
        return (sub1, --applySubDeriv sub1
                    deriv : derivs))
    `catchError`
    (\msg -> deriveSubByAsm derivsAll derivs
             infRules (judg:judgs) varSet)
