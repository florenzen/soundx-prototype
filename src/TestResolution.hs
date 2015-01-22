module TestResolution where

import qualified Data.Set as S
import           Derive
import           SimpleTypes
import           Syntax
import           Validation
import           Variables


test01 :: Judg
test01 = tj envnil (tmnum (lnat "1")) vU

test02 :: Judg
test02 = tj envnil (tmadd (tmnum (lnat "1")) (tmnum (lnat "1"))) vU

test03 :: Judg
test03 = tj envnil (tmadd (tmnum (lnat "1")) (tmvar (lid "x"))) vU

test04 :: Judg
test04 = tj (envtm (envtm envnil (lid "b") (tyfun tynat tynat)) (lid "a") tynat)
         (tmvar (lid "b")) vU

test05 :: Judg
test05 = tj (envtm (envtm envnil (lid "b") (tyfun tynat tynat)) (lid "a") tynat)
         (tmvar (lid "a")) vU

test06 :: Judg
test06 = tj (envtm (envtm envnil (lid "b") (tyfun tynat tynat)) (lid "a") tynat)
         (tmvar (lid "c")) vU

test07 :: Judg
test07 = tj (envtm (envtm (envtm envnil
                           (lid "a") tybool)
                    (lid "b") (tyfun tynat tybool))
             (lid "c") tynat)
         (tmvar (lid "b")) vU

-- \x:Nat->Nat. add (add 1 x) x
test08 :: Judg
test08 = tj envnil (tmabs (lid "x") (tyfun tynat tynat)
                    (tmadd (tmadd (tmnum (lnat "1")) (tmvar (lid "x"))) (tmvar (lid "x")))) vU

test09 :: Judg
test09 = tj envnil (tmadd (tmapp (tmnum (lnat "3")) (tmnum (lnat "2"))) (tmnum (lnat "1"))) vU

test10 :: Judg
test10 = tj envnil (tmadd (tmapp (tmabs (lid "a") tybool (tmnum (lnat "5")))
                           (tmnum (lnat "2"))) (tmnum (lnat "1"))) vU

test11 :: Judg
test11 = tj envnil (tmadd (tmapp (tmabs (lid "a") tybool (tmnum (lnat "5")))
                           (tmnum (lnat "2"))) tmfalse) vU


test12 :: Judg
test12 = tj envnil (tmabs (lid "a") tybool (tmadd (tmvar (lid "a")) (tmnum (lnat "6")))) vU

test13 :: Either [Deriv] Deriv
test13 = Derive.buildDerivation [] infRulesST
       (sj
        (repcons (lmid "modF") (envtm envnil (lid "x") tynat) repnil)
        (md (lmid "moda")
         (impcons (imp (lmid "modF"))
          impnil)
         (dfcons (lid "a") (tmnum (lnat "1"))
          (dfcons (lid "a") (tmnum (lnat "1"))
           dfnil)))
        vC)

test14 :: Either [Deriv] Deriv
test14 = Derive.buildDerivation [] infRulesST
        (ij
         (repcons (lmid "modF") (envtm envnil (lid "x") tynat) repnil)
         (impcons (imp (lmid "modF"))
          impnil)
         vC)

test15 :: Either [Deriv] Deriv
test15 = Derive.buildDerivation [] infRulesST
       (dj
        (envtm envnil (lid "x") tynat)
        (dfcons (lid "a") (tmnum (lnat "1"))
         (dfcons (lid "b") (tmnum (lnat "1"))
          dfnil)) vC)

test16 :: Judg
test16 = fj vx (envtm envnil (lid "a") tynat)

testDerive :: Judg -> [Answer]
testDerive judg = deriveAns S.empty [] infRulesST [] judg

testBuildDerivation :: Judg -> ([Deriv], [()])
testBuildDerivation judg =
    let derivs = case buildDerivation [] infRulesST judg of
                   Left derivs -> derivs
                   Right deriv -> [deriv]
        valid = map validateDeriv derivs
    in (derivs, valid)
  where
    validateDeriv deriv =
        if validate [] infRulesST deriv then () else
            error $ "** invalid derivation **" ++ show deriv
