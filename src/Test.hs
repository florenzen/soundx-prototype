module Test where

-- import Debug.Trace

import           Prelude hiding (mod)
import           Test.HUnit

import           Syntax
import           Derive
import           Rewrite
import           Validation
import           Verification
import           WFBase
import           WFMod
import           CompileMod

testCaseDeriveDesugar :: Base -> (String, [Ext], Judg) -> Test
testCaseDeriveDesugar base (label,exts,judg) =
    label ~: TestCase (assertionDeriveDesugar base exts judg)

assertionDeriveDesugar :: Base -> [Ext] -> Judg -> Assertion
assertionDeriveDesugar base [] judg =
    let infRules = getBaseInfRules base
    in case derive [] infRules judg of
        Left msg -> assertFailure ("Judgment " ++ show judg ++ " not derived")
        Right deriv ->
            assertBool ("Derivation for " ++ show judg ++ " not valid")
                         (validate [] infRules deriv)
assertionDeriveDesugar base exts judg =
    let infRulesX = concatMap getExtInfRules exts
        infRules = getBaseInfRules base
        infRulesAll = infRulesX ++ infRules
    in case derive [] infRulesAll judg of
         Left msg -> assertFailure ("Judgment " ++ show judg ++ " not derived")
         Right deriv ->
             let deriv' = desugar base exts deriv
                 derivResult = either (const False) (const True)
                               (derive [] infRules (concl deriv'))
                 validateResult = validate [] infRules deriv'
             in assertBool ("Could not derive or validate result " ++
                            "of desugaring in B: " ++ show (concl deriv'))
                    (validateResult && derivResult)


testCaseVerifyExtension :: Base -> (String, Ext, [Ext]) -> Test
testCaseVerifyExtension base (label,ext,exts) =
    let assertion =
            case verify base exts ext of
              Left msg -> assertFailure msg
              Right () -> return ()
    in label ~: assertion

testCaseRejectExtension :: Base -> (String, Ext, [Ext]) -> Test
testCaseRejectExtension base (label,ext,exts) =
    let assertion =
            case verify base exts ext of
              Left msg -> return ()
              Right () -> assertFailure "Wrong extension accepted"
    in label ~: assertion

testCaseWfBase :: (String, Base) -> Test
testCaseWfBase (label,base) =
    let assertion =
            case wfBase base of
              Right () -> return ()
              Left msg -> assertFailure $ "Base system not well-formed: " ++ msg
    in label ~: assertion

testCaseWfMod :: Base -> (String, [Intf], Mod) -> Test
testCaseWfMod base (label,intfs,mod) =
    let assertion =
            case wfMod intfs base mod of
              Right _ -> return ()
              Left msg -> assertFailure $ "Module not well-formed: " ++ msg
    in label ~: assertion

testCaseWfModReject :: Base -> (String, [Intf], Mod) -> Test
testCaseWfModReject base (label,intfs,mod) =
    let assertion =
            case wfMod intfs base mod of
              Left _ -> return ()
              Right _ -> assertFailure $ "Ill-formed module accepted"
    in label ~: assertion

testCaseCompMod :: Base -> (String, [Intf], Mod) -> Test
testCaseCompMod base (label,intfs,mod) =
    let assertion =
            case compileMod base intfs mod of
              Right _ -> return ()
              Left msg -> assertFailure $ "Could not compile module: " ++ msg
    in label ~: assertion
