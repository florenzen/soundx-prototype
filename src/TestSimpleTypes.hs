module TestSimpleTypes where

import Test.HUnit
import Prelude hiding (mod)
import Data.Either.Utils

import qualified Driver as D
import SimpleTypes
import SimpleTypesExtensions
import Variables
import Test
import Syntax
import WFMod


texDerive :: (t, [Ext], Judg) -> IO ()
texDerive (_,exts,judg) =
    D.derive True exts baseST judg

texDeriveDesugar :: (t, [Ext], Judg) -> IO ()
texDeriveDesugar (_,exts,judg) =
    D.deriveDesugar True exts baseST judg

derive :: (t, [Ext], Judg) -> IO ()
derive (_,exts,judg) =
    D.derive False exts baseST judg

compileMod :: (t, [Intf], Mod) -> IO ()
compileMod (_,intfs,mod) =
    D.compileMod False baseST intfs mod

texCompileMod :: (t, [Intf], Mod) -> IO ()
texCompileMod (_,intfs,mod) =
    D.compileMod True baseST intfs mod

deriveMod :: (t, [Intf], Mod) -> IO ()
deriveMod (_,intfs,mod) =
    D.deriveMod False baseST intfs mod

texDeriveMod :: (t, [Intf], Mod) -> IO ()
texDeriveMod (_,intfs,mod) =
   D.deriveMod True baseST intfs mod

deriveDesugar :: (t, [Ext], Judg) -> IO ()
deriveDesugar (label,exts,judg) =
    D.deriveDesugar False exts baseST judg

verify :: (t, Ext, [Ext]) -> IO ()
verify (label,ext,exts) =
    D.verify ext exts baseST

runTestSuite :: IO Counts
runTestSuite = runTestTT testSuite

testSuite :: Test
testSuite =
    TestList $
      (map (testCaseDeriveDesugar baseST)
           testCasesDeriveDesugar) ++
      (map (testCaseVerifyExtension baseST)
           testCasesVerifyExtension) ++
      (map (testCaseRejectExtension baseST)
           testCasesRejectExtension) ++
      (map testCaseWfBase testCasesWfBase) ++
      (map (testCaseWfMod baseST)
           testCasesWfMod) ++
      (map (testCaseWfModReject baseST)
           testCasesWfModReject) ++
      (map (testCaseCompMod baseST)
           testCasesCompMod)

-- Accepted base systems

testCasesWfBase :: [(String, Base)]
testCasesWfBase = [
 testW01
 ]

testW01 :: (String, Base)
testW01 = ("ST",baseST)

-- Accepted modules

testCasesWfMod :: [(String, [Intf], Mod)]
testCasesWfMod = [
 testM01,
 testM02,
 testM03,
 testM04,
 testM05,
 testM06,
 testM07,
 testM08,
 testM09,
 testM10,
 testM11,
 testM12
 ]

intf :: [Intf] -> Mod -> Intf
intf intfs = (fromRight . intfMod intfs baseST)
testM01mod :: Mod
testM01mod = Mod (md modA
                  impnil
                  dfnil
                 )
             extEmpty
testM01intf :: Intf
testM01intf = intf [] testM01mod
testM01 :: (String, [a], Mod)
testM01 = ("A: empty module",
           [],
           testM01mod
          )

-- module B
-- val a = num
-- val b = num
testM02mod :: Mod
testM02mod = Mod (md modB
                  impnil
                  (dfcons evA tmnum
                  (        dfcons evB tmnum dfnil)
                   -- (dfcons evB (tmadd (tmvar evA) tmnum)
                   --  dfnil)
                  )
                 )
             extEmpty
testM02intf :: Intf
testM02intf = intf [] testM02mod
testM02 :: (String, [a], Mod)
testM02 = ("B: two definitions",
           [],
           testM02mod
          )

-- module C
-- import B
-- val c = (\a:Nat. a) a
testM03mod :: Mod
testM03mod = Mod (md modC
                  (impcons (imp modB) impnil)
                  (dfcons evC (tmapp (tmabs evA tynat (tmvar evA)) (tmvar evA))
                   dfnil
                  )
                 )
             extEmpty
testM03intf :: Intf
testM03intf = intf [testM02intf] testM03mod
testM03 :: (String, [Intf], Mod)
testM03 = ("C: import B",
           [testM02intf],
           testM03mod
          )

-- module D
-- import B
-- import C
-- val d = (\a:Nat.e) num
-- val e = num
testM04mod :: Mod
testM04mod = Mod (md modD
                  (impcons (imp modB)
                   (impcons (imp modC) impnil))
                  (dfcons evD (tmapp (tmabs evA tynat (tmvar evA)) (tmnum))
                   (dfcons evE (tmnum)
                    dfnil)
                  )
                 )
             extEmpty
testM04intf :: Intf
testM04intf = intf [testM02intf,testM03intf] testM04mod
testM04 :: (String, [Intf], Mod)
testM04 = ("D: import B, C",
           [testM02intf,testM03intf],
           testM04mod
          )

-- module modA
-- // let extension
testM05mod :: Mod
testM05mod = Mod (md modA
                  impnil
                  dfnil)
             extLet
testM05intf :: Intf
testM05intf = intf [] testM05mod
testM05 :: (String, [a], Mod)
testM05 = ("A: LetExtension",
           [],
           testM05mod)

-- module modB
-- import A // let extension
-- import D // defines d e
-- val a = let b = d + num in b + num
-- val b = a + num
testM06mod :: Mod
testM06mod = Mod (md modB
                  (impcons (imp modA)
                   (impcons (imp modD)
                    impnil))
                  (dfcons evA (tmlet evB (tmadd (tmvar evD) tmnum)
                                         (tmadd (tmvar evB) tmnum))
                   (dfcons evB (tmadd (tmvar evA) tmnum)
                    dfnil))
                 )
             extEmpty
testM06intf :: Intf
testM06intf = intf [testM05intf,testM04intf] testM06mod
testM06 :: (String, [Intf], Mod)
testM06 = ("B: use let extension",
           [testM05intf,testM04intf],
           testM06mod)

-- module C
-- import A // defines let extension
-- import B // uses let extension, hence also exports it, defines a, b
-- val c = num + (let d = a in d)
testM07mod :: Mod
testM07mod = Mod (md modC
               (impcons (imp modA)
                (impcons (imp modB)
                 impnil))
               (dfcons evC (tmadd tmnum
                            (tmlet evD (tmvar evA) (tmvar evD)))
                dfnil))
          extEmpty
testM07intf :: Intf
testM07intf = intf [testM05intf,testM06intf] testM07mod
testM07 :: (String, [Intf], Mod)
testM07 = ("C: import A and B",
           [testM05intf,testM06intf],
           testM07mod)

-- module B
-- import A // defines let extension
-- // define or extension which uses let
testM08mod :: Mod
testM08mod = Mod (md modB
                  (impcons (imp modA)
                   impnil)
                  dfnil)
             extOr
testM08intf :: Intf
testM08intf = intf [testM05intf] testM08mod
testM08 :: (String, [Intf], Mod)
testM08 = ("B: defines or and uses let",
           [testM05intf],
           testM08mod)

-- module B
-- import A // defines let extension
-- // define letfun1 extension which uses let
testM09mod :: Mod
testM09mod = Mod (md modB
                  (impcons (imp modA)
                   impnil)
                  dfnil)
             extLetFun1
testM09intf :: Intf
testM09intf = intf [testM05intf] testM09mod
testM09 :: (String, [Intf], Mod)
testM09 = ("B: defines or and uses let",
           [testM05intf],
           testM09mod)

-- module A
-- // define letstar
testM10mod :: Mod
testM10mod = Mod (md modA impnil dfnil)
             extLetstar
testM10intf :: Intf
testM10intf = intf [] testM10mod
testM10 :: (String, [a], Mod)
testM10 = ("A: defines letstar",
           [],
           testM10mod)

-- module B
-- // define pair
testM11mod :: Mod
testM11mod = Mod (md modB impnil dfnil)
             extPair
testM11intf :: Intf
testM11intf = intf [] testM11mod
testM11 :: (String, [a], Mod)
testM11 = ("B: defines pair",
           [],
           testM11mod)

-- module C
-- import A // defines letstar
-- import B // defines pair
-- // define pair bindings with decomposition
testM12mod :: Mod
testM12mod = Mod (md modC
                  (impcons (imp modA)
                   (impcons (imp modB)
                    impnil))
                  dfnil)
             (Ext aritiesLetstarP infRulesLetstarP [] resRRsLetstarP)
testM12intf :: Intf
testM12intf = intf [testM10intf,testM11intf] testM12mod
testM12 :: (String, [Intf], Mod)
testM12 = ("C: defines pair bindings, imports letstar and pair",
           [testM10intf,testM11intf],
           testM12mod)


-- Rejected modules

testCasesWfModReject :: [(String, [a], Mod)]
testCasesWfModReject = [
 testMR01
 ]

-- module A
-- // define let and letnat with syntactic overlap
testMR01mod :: Mod
testMR01mod = Mod (md modA
                  impnil
                  dfnil)
              (Ext (aritiesLet++aritiesLetNat)
                       (infRulesLet++infRulesLetNat)
                       univRRsLetNat resRRsLet)
testMR01intf :: Intf
testMR01intf = intf [] testMR01mod
testMR01 :: (String, [a], Mod)
testMR01 = ("A: defines let and letnat",
            [],
            testMR01mod)


-- Compiled modules
testCasesCompMod :: [(String, [Intf], Mod)]
testCasesCompMod = [
 testC01,
 testC02,
 testC03
 ]

testC01mod :: Mod
testC01mod = Mod (md modA
                  (impcons (imp modB) impnil)
                  (dfcons evA (tmsnd (tmpair tmnum tmnum))
                   (dfcons evB (tmpair tmtrue tmfalse)
                    (dfcons evC (tmif (tmsnd (tmvar evB)) tmnum tmnum)
                     dfnil))))
             extEmpty
testC01intf :: Intf
testC01intf = intf [testM11intf] testC01mod
testC01 :: (String, [Intf], Mod)
testC01 = ("use pair",
           [testM11intf],
           testC01mod
          )

testC02mod :: Mod
testC02mod = Mod (md modC
                  (impcons (imp modA) impnil)
                  (dfcons evD (tmvar evB)
                   (dfcons evE (tmsnd (tmvar evD))
                    dfnil)))
             extEmpty
testC02 :: (String, [Intf], Mod)
testC02 = ("use module A (with pair)",
           [testC01intf],
           testC02mod)

testC03mod :: Mod
testC03mod = Mod (md modD
                  (impcons (imp modA) impnil)
                  dfnil)
             extLetstarBL
testC03intf :: Intf
testC03intf = intf [testM05intf] testC03mod
testC03 :: (String, [Intf], Mod)
testC03 = ("define let* using imported let",
           [testM05intf],
           testC03mod)

testC04mod :: Mod
testC04mod = Mod (md modE
                  (impcons (imp modD) -- import letstarBL
                   (impcons (imp modB) impnil)) -- import pair
                  (dfcons evE
                   (tmadd
                    (tmletstarbl (bdgconsbl evA (tmpair (tmadd tmnum tmnum) tmnum)
                                  (bdgconsbl evB (tmfst (tmvar evA))
                                   (bdgconsbl evC (tmsnd (tmvar evA)) bdgnilbl)))
                     (tmadd (tmvar evB) (tmvar evC)))
                    tmnum)
                   dfnil))
             extEmpty
testC04 :: (String, [Intf], Mod)
testC04 = ("use let* defined by let",
           [testC03intf,testM11intf],
           testC04mod)

-- Accepted extensions

testCasesVerifyExtension :: [(String, Ext, [Ext])]
testCasesVerifyExtension = [
 testX01,
 testX02,
 testX03,
 testX04,
 testX05,
 testX06,
 testX07,
 testX08,
 testX09,
 testX10,
 testX11,
 testX12
 ]

testX01 :: (String, Ext, [a])
testX01 = ("Let",extLet,[])
testX02 :: (String, Ext, [a])
testX02 = ("NatPair",extNatPair,[])
testX03 :: (String, Ext, [Ext])
testX03 = ("Or",extOr,[extLet])
testX04 :: (String, Ext, [Ext])
testX04 = ("Letfun1",extLetFun1,[extLet])
testX05 :: (String, Ext, [a])
testX05 = ("Letstar",extLetstar,[])
testX06 :: (String, Ext, [Ext])
testX06 = ("LetstarNNvalid",extLetstarNNValid,[extNatPair])
testX07 :: (String, Ext, [Ext])
testX07 = ("Double",extDouble,[extNatPair])
testX08 :: (String, Ext, [a])
testX08 = ("Pair",extPair,[])
testX09 :: (String, Ext, [a])
testX09 = ("RedefPlusU",extRedefPlusU,[])
testX10 :: (String, Ext, [a])
testX10 = ("RedefPlusR",extRedefPlusR,[])
testX11 :: (String, Ext, [a])
testX11 = ("LetNat",extLetNat,[])
testX12 :: (String, Ext, [a])
testX12 = ("extEmpty",extEmpty,[])

-- Rejected extensions

testCasesRejectExtension :: [(String, Ext, [a])]
testCasesRejectExtension = [
 testR01,
 testR02,
 testR03,
 testR04,
 testR05,
 testR06,
 testR07
 ]

testR01 :: (String, Ext, [a])
testR01 = ("LetWrong1",
           Ext aritiesLet infRulesLetWrong1 [] resRRsLetWrong1,
           [])
testR02 :: (String, Ext, [a])
testR02 = ("LetWrong2",
           Ext aritiesLet infRulesLetWrong2 [] resRRsLetWrong2,
           [])
testR03 :: (String, Ext, [a])
testR03 = ("LetstarNNWrong",extLetstarNNWrong,[])
testR04 :: (String, Ext, [a])
testR04 = ("LetAnnoWrong1",extLetAnnoWrong1,[])
testR05 :: (String, Ext, [a])
testR05 = ("LetAnnoWrong2",extLetAnnoWrong2,[])
testR06 :: (String, Ext, [a])
testR06 = ("LetstarPWrong",extLetstarP,[])
testR07 :: (String, Ext, [a])
testR07 = ("extWhere",extWhere,[])


testCasesDeriveDesugar :: [(String, [Ext], Judg)]
testCasesDeriveDesugar = [
 test01,
 test02,
 test03,
 test04,
 test05,
 test06,
 test07,
 test08,
 test09,
 test10,
 test10a,
 test10b,
 test10c,
 test11,
 test11a,
 test12,
 test13,
 test14,
 test15,
 test16,
 test17,
 test18,
 test19,
 test20,
 test21,
 test22,
 -- test27,
 -- test28,
 test30,
 test31,
 test32,
 test33,
 test34
 ]

test01 :: (String, [a], Judg)
test01 =
    ("test01",
     [],
     tj envnil (tmapp (tmabs evA tybool (tmvar evA)) tmtrue) tybool)

test02 :: (String, [a], Judg)
test02 =
    ("test02",
     [],
     tj envnil (tmapp (tmabs evA tybool (tmvar evA)) tmtrue) vU)

test03 :: (String, [a], Judg)
test03 =
    ("test03",
     [],
     tj (envtm envnil evB tybool) (tmapp (tmabs evA tybool (tmvar evB)) tmtrue) vU)

test04 :: (String, [a], Judg)
test04 =
    ("test04",
     [],
     tj (envtm (envtm (envtm envnil evA tybool) evB (tyfun tynat tybool)) evC tynat)
       (tmvar evB) vU)

test05 :: (String, [a], Judg)
test05 =
    ("test05",
     [],
     fj evA (envtm envnil evB tybool))

test06 :: (String, [Ext], Judg)
test06 =
    ("test06",
     [extLet],
     tj envnil (tmlet evA tmnum (tmvar evA)) vU)

test07 :: (String, [Ext], Judg)
test07 =
    ("test07",
     [extLet],
     tj (envtm envnil evA tybool) (tmlet evA tmnum (tmvar evA)) vU)

test08 :: (String, [Ext], Judg)
test08 =
    ("test08",
     [extLet],
     tj (envtm envnil evB tynat)
       (tmadd (tmvar evB) (tmlet evA tmnum (tmvar evA))) vU)

test09 :: (String, [Ext], Judg)
test09 =
    ("test09",
     [extNatPair],
     tj (envtm envnil evA tynatpair) (tmvar evA) vU)

test10 :: (String, [Ext], Judg)
test10 =
    ("test10",
     [extNatPair],
     tj envnil (tmnatpair tmnum tmnum) vU)

test10a :: (String, [Ext], Judg)
test10a =
    ("test10a",
     [extNatPair],
     tj (envtm envnil evA tybool) (tmnatpair tmnum tmnum) vU)

test10b :: (String, [Ext], Judg)
test10b =
    ("test10b",
     [extNatPair],
     tj (envtm (envtm envnil evB tynat) evA tybool) (tmnatpair (tmvar evB) tmnum) vU)

test10c :: (String, [Ext], Judg)
test10c =
    ("test10c",
     [extNatPair],
     tj (envtm (envtm (envtm envnil evE (tyfun tynatpair tynat)) evB tynat)
              evA tybool)
            (tmapp (tmvar evE) (tmnatpair (tmvar evB) tmnum)) vU)

test10d :: (String, [Ext], Judg)
test10d =
    ("test10d",
     [extNatPair],
     tj (envtm envnil evA tybool) (tmabs evA tynat
                                 (tmnatpair (tmvar evA) tmnum)) vU)

test11 :: (String, [Ext], Judg)
test11 =
    ("test11",
     [extNatPair],
     tj envnil (tmnatsnd (tmnatpair tmnum tmnum)) vU)

test11a :: (String, [Ext], Judg)
test11a =
    ("test11a",
     [extNatPair],
     tj envnil (tmnatsnd (tmnatpair tmnum tmnum)) vU)

test12 :: (String, [Ext], Judg)
test12 =
    ("test12",
     [extNatPair],
     tj envnil (tmabs evA tynat (tmnatpair tmnum (tmvar evA))) vU)

test13 :: (String, [Ext], Judg)
test13 =
    ("test13",
     [extNatPair],
     tj envnil (tmnatpair tmnum tmnum) vU)

test14 :: (String, [Ext], Judg)
test14 =
    ("test14",
     [extNatPair,extLet],
     tj envnil (tmlet evA (tmnatpair tmnum tmnum) (tmnatfst (tmvar evA))) vU)

test15 :: (String, [Ext], Judg)
test15 =
    ("test15",
     [extOr,extLet],
     tj (envtm envnil evA tybool) (tmor tmtrue (tmvar evA)) vU)

test16 :: (String, [Ext], Judg)
test16 =
    ("test16",
     [extLetFun1,extLet],
     tj envnil (tmletfun1 evA evB tynat (tmvar evB) (tmapp (tmvar evA) tmnum)) vU)

test17 :: (String, [Ext], Judg)
test17 =
    ("test17",
     [extLetFun1,extLet],
     tj envnil
     (tmadd (tmletfun1 evA evB tynat (tmvar evB)
             (tmapp (tmvar evA) tmnum)) tmnum)
      vU)

test18 :: (String, [Ext], Judg)
test18 =
    ("test18",
     [extLetstar],
     tj envnil
     (tmletstar (bdgcons evA tmtrue (bdgcons evB (tmvar evA) bdgnil))
     (tmif (tmvar evB) tmnum tmnum))
     vU)

-- ∅ ⊢ (let a = true; b = a in if b then n else n) + n : Nat
test19 :: (String, [Ext], Judg)
test19 =
    ("test19",
     [extLetstar],
     tj envnil
     (tmadd (tmletstar (bdgcons evA tmtrue (bdgcons evB (tmvar evA) bdgnil))
      (tmif (tmvar evB) tmnum tmnum)) tmnum)
     vU)

test20 :: (String, [Ext], Judg)
test20 =
    ("test20",
     [extLetstar],
     tj envnil
     (tmletstar (bdgcons evA tmtrue bdgnil)
     (tmif (tmvar evA) tmnum tmnum))
     vU)

test21 :: (String, [Ext], Judg)
test21 =
    ("test21",
     [extLetstar,extNatPair],
     tj envnil
        (tmletstar (bdgcons evA (tmnatpair (tmadd tmnum tmnum) tmnum)
                    (bdgcons evB (tmnatfst (tmvar evA))
                     (bdgcons evC (tmnatsnd (tmvar evA)) bdgnil)))
         (tmadd (tmvar evB) (tmvar evC)))
        vU)

test22 :: (String, [Ext], Judg)
test22 =
    ("test22",
     [extLetstar,extNatPair],
     tj (envtm envnil evA tybool)
        (tmadd
         (tmletstar (bdgcons evA (tmnatpair (tmadd tmnum tmnum) tmnum)
                     (bdgcons evB (tmnatfst (tmvar evA))
                      (bdgcons evC (tmnatsnd (tmvar evA)) bdgnil)))
          (tmadd (tmvar evB) (tmvar evC)))
         tmnum)
        vU)

-- Forgotten rewrite rule
-- test23 =
--     ("test23",
--      infRulesNatPair,
--      drop 1 rewRulesNatPair,
--      tj (envtm envnil evA tynatpair) (tmvar evA) tynatpair)

-- For (bogus) T-NatPairWeak rule
test24 :: (String, [Ext], Judg)
test24 =
    ("test24",
     [extNatPair],
     tj (envtm (envtm envnil evB tynat) evA tybool)
            (tmnatfst (tmnatpair (tmvar evB) tmnum)) vU)
test25 :: (String, [Ext], Judg)
test25 =
    ("test25",
     [extNatPair],
     tj (envtm (envtm envnil evB tynat) evA tynatpair)
            (tmnatpair (tmvar evB) tmnum) vU)
test26 :: (String, [Ext], Judg)
test26 =
    ("test26",
     [extNatPair],
     tj (envtm (envtm envnil evB tynat) evA tynatpair)
            (tmnatsnd (tmnatpair tmnum tmnum)) vU)

test27 :: (String, [Ext], Judg)
test27 =
    ("test27",
     [extLetstarP],
     tj envnil (tmadd tmnum (tmfst (tmpair tmnum tmnum))) vU)

-- This one does not fail during desugaring and
-- the used part of the extension would be accepted
-- by verification
test28 :: (String, [Ext], Judg)
test28 =
    ("test28",
     [extLetstarP],
     tj envnil (tmletstar
                (bdgpair evA evB (tmpair tmnum tmnum)
                 (bdgcons evC (tmvar evB) bdgnil))
                (tmadd tmnum (tmvar evC))) vU)

-- This one fails during desugaring. But extension is not
-- accepted during verification
-- test29 =
--     ("test29",
--      [extLetstarP],
--      tj envnil (tmletstar
--                 (bdgpair evA evB (tmpair tmnum tmnum) bdgnil) (tmvar evB)) vU)

test30 :: (String, [Ext], Judg)
test30 =
    ("test30",
     [extRedefPlusU],
      tj envnil (tmadd tmnum tmnum) vU)

test31 :: (String, [Ext], Judg)
test31 =
    ("test31",
     [extRedefPlusU],
      tj envnil (tmapp (tmabs evA tynat (tmvar evA)) (tmadd tmnum tmnum)) vU)

test32 :: (String, [Ext], Judg)
test32 =
    ("test32",
     [extRedefPlusU],
      tj envnil (tmadd tmnum tmnum) vU)

test33 :: (String, [Ext], Judg)
test33 =
    ("test33",
     [extRedefPlusR],
      tj envnil (tmapp (tmabs evA tynat (tmvar evA)) (tmadd tmnum tmnum)) vU)

test34 :: (String, [Ext], Judg)
test34 =
    ("test34",
     [extLetstar,extPair],
     tj (envtm envnil evA tybool)
        (tmadd
         (tmletstar (bdgcons evA (tmpair (tmadd tmnum tmnum) tmnum)
                     (bdgcons evB (tmfst (tmvar evA))
                      (bdgcons evC (tmsnd (tmvar evA)) bdgnil)))
          (tmadd (tmvar evB) (tmvar evC)))
         tmnum)
        vU)

test35 :: (String, [Ext], Judg)
test35 =
    ("test35",
     [extWhere],
     tj envnil
        (tmwhere (tmadd (tmvar evB) (tmvar evA))
         (bdgcons evA tmnum
          (bdgcons evB (tmvar evA)
           (bdgcons evC (tmadd tmnum (tmvar evB))
            bdgnil))))
     vU)
