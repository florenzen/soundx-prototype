module TestSystemF where

import Test.HUnit

import qualified Driver as D
import SystemF
import SystemFExtensions
import Variables
import Test


texDerive (label,infRuleList,rewRuleList,judg) =
    D.derive True (infRuleList ++ infRuleListSF) judg

texDeriveDesugar (label,infRuleList,rewRuleList,judg) =
    D.deriveDesugar True infRuleList infRuleListSF rewRuleList judg

derive (label,infRuleList,rewRuleList,judg) =
    D.derive False (infRuleList ++ infRuleListSF) judg

deriveDesugar (label,infRuleList,rewRuleList,judg) =
    D.deriveDesugar False infRuleList infRuleListSF rewRuleList judg

deriveDesugarJudg (label,infRuleList,rewRuleList,judg) =
    D.deriveDesugarJudg False infRuleList infRuleListSF rewRuleList judg

verify infRuleList rewRuleList =
    D.verify infRuleList rewRuleList infRuleListSF

runTestSuite = runTestTT testSuite

testSuite =
    TestList $
      -- (map (testCaseDeriveDesugar infRuleListSF)
      --      testCasesDeriveDesugar) ++
      (map (testCaseDeriveDesugarJudg infRuleListSF)
           testCasesDeriveDesugar) ++
      (map (testCaseVerifyExtension infRuleListSF)
           testCasesVerifyExtension)

testCasesVerifyExtension = [
 testX01
 ]

testX01 = ("Pair",infRuleListPair,rewRuleListPair)

testCasesDeriveDesugar = [
 test01,
 test01a,
 test01b,
 test01c,
 test02,
 test02a,
 test03,
 test04,
 test04a,
 test04b,
 test05,
 test06,
 test07
 ]

-- Tests for substitution

test01 =
    ("test01",
     [],[],
     sj (envty (envty (envty envnil evA) evA1) evA2) vU evA (tyfun evA1 evA2)
            (tyforall evB (tyforall evC
                           (tyfun (tyvar evA) (tyfun (tyvar evB) (tyvar evC))))))

test01a =
    ("test01a",
     [],[],
     sj (envty (envty (envty envnil evA) evA1) evA2) vU evA (tyfun evA1 evA2)
            (tyforall evA1 (tyforall evA2
                           (tyfun (tyvar evA) (tyfun (tyvar evA1) (tyvar evA2))))))

test01b =
    ("test01b",
     [],[],
     sj (envty envnil evA) vU evA tynat (tyforall evA (tyforall evB tynat)))

test01c =
    ("test01c",
     [],[],
     sj (envty envnil evA) vU evA tynat
            (tyforall evA (tyforall evB (tyfun (tyvar evA) (tyvar evB)))))

test02 =
    ("test02",
     [],[],
     sj (envty envnil evA) vU evA tybool (tyfun tynat (tyvar evA)))

test02a =
    ("test02a",
     [],[],
     sj (envty (envty envnil evB) evA) vU evA tybool (tyfun tynat (tyvar evB)))

test02b =
    ("test02b",
     [],[],
     sj (envty (envty envnil evB) evA) vU evA tybool
            (tyfun (tyfun tynat (tyvar evA)) (tyvar evA)))

test03 =
    ("test03",
     [],[],
     sj (envty envnil evA) vU evA tynat
            (tyforall evB (tyfun (tyvar evA) (tyvar evB))))


-- Tests for base system typing

test04 =
    ("test04",
     [],[],
     tj envnil (tmtapp (tmtabs evE (tmabs evA (tyvar evE) (tmvar evA))) tynat)
            (tyfun tynat tynat))

test04a =
    ("test04a",
     [],[],
     tj envnil (tmtabs evE (tmabs evA (tyvar evE) (tmvar evA))) vU)

test04b =
    ("test04b",
     [],[],
     tj (envtm envnil evA (tyvar evE)) (tmabs evA (tyvar evE) (tmvar evA)) vU)


-- Tests for pairs

test05 =
    ("test05",
     infRuleListPair,rewRuleListPair,
     tj envnil (tmpair tmnum tmtrue) vU)

test06 =
    ("test06",
     infRuleListPair,rewRuleListPair,
     tj envnil (tmsnd (tmpair tmnum tmtrue)) vU)

test07 =
    ("test07",
     infRuleListPair,rewRuleListPair,
     tj envnil (tmif (tmsnd (tmpair tmnum tmtrue)) tmnum (tmadd tmnum tmnum)) vU)
