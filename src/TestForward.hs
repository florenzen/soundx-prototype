module TestForward where

import           Data.Either.Utils
import qualified Data.Set as S

import           Derive
import           Forward
import           Rewrite
import           SimpleTypes
import           SimpleTypesExtensions
import           Syntax
import           Validation
import           Variables


prepare infRule ext infRulesOtherExts =
    let infRule' = desugarInfRule (getExtUnivRRs ext) (getExtResRRs ext)
                   (getInfRuleJudgsP infRule, getInfRuleJudgC infRule)
        deriv = head $ fromRight $
                let derivsAsm = map Asm (fst infRule')
                in derive derivsAsm (infRulesST++infRulesOtherExts) [snd infRule'] S.empty
    in (infRule,infRule',deriv)

forw derivs (infRule,infRule',deriv) =
    fromRight $ forward baseST derivs infRule' deriv

valid = validate [] (getBaseInfRules baseST)




tPair = prepare (infRulesPair !! 0) extPair []

tPairDerivAsm =
    head $
    let exprTm = tmadd tmnum tmnum
        exprEnv = envtm envnil evG (tyfun tynat (tyfun tynat tynat))
    in fromRight $
       derive [] infRulesST [tj exprEnv exprTm tynat] S.empty

tPairForward = forw [tPairDerivAsm,tPairDerivAsm] tPair


tLetstarCons = prepare (infRulesLetstar !! 0) extLetstar []

tLetstarDerivAsm1 =
    head $
    fromRight $
    derive [] infRulesST [tj envnil tmnum tynat] S.empty

tLetstarDerivAsm2 =
    head $
    let exprTm = tmapp (tmabs evB tynat tmnum) tmnum
        exprEnv = envtm envnil evA tynat
    in fromRight $
       derive [] (infRulesST++getExtInfRules extLetstar)
                  [tj exprEnv exprTm tynat] S.empty

tLetstarForward = forw [tLetstarDerivAsm1,tLetstarDerivAsm2] tLetstarCons


addExt (Ext a1 i1 r1 u1) (Ext a2 i2 r2 u2) = Ext (a1++a2) (i1++i2) (r1++r2) (u1++u2)


tNatPair = prepare (infRulesNatPair !! 0) extNatPair []
