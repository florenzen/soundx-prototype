module TestSimpleTypes where

import           Test.HUnit
import           Prelude hiding (mod)

import qualified Driver as D
import           SimpleTypes
import           SimpleTypesExtensions
import           Syntax
import           Test
import           Variables
import           WFMod
import Utils


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

runTestSuite :: IO ()
runTestSuite = do
    runTestText (PutText (\line _ _ -> putStrLn line) ()) testSuite
    return ()

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
 -- testM08,
 testM09,
 testM10,
 testM11,
 testM12
 ]

intf :: [Intf] -> Mod -> Intf
intf intfs = (fromRight . intfMod intfs baseST)
testM01mod :: Mod
testM01mod = Mod (md (lmid "modA")
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
testM02mod = Mod (md (lmid "modB")
                  impnil
                  (dfcons (lid "a") (tmnum (lnat "5"))
                  (        dfcons (lid "b") (tmnum (lnat "7")) dfnil)
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
testM03mod = Mod (md (lmid "modC")
                  (impcons (imp (lmid "modB")) impnil)
                  (dfcons (lid "c")
                          (tmnum (lnat "1"))
                  -- (dfcons (lid "c")
                  --  (tmapp (tmabs (lid "a") tynat (tmvar (lid "a"))) (tmvar (lid "a")))
                   dfnil
                  )
                 )
             extEmpty
testM03intf :: Intf
testM03intf = intf [testM02intf] testM03mod
testM03 :: (String, [Intf], Mod)
testM03 = ("C: import B",
           [Intf (lmid "modB") envnil []], -- testM02intf],
           testM03mod
          )

-- module D
-- import B
-- import C
-- val d = (\a:Nat.e) num
-- val e = num
testM04mod :: Mod
testM04mod = Mod (md (lmid "modD")
                  (impcons (imp (lmid "modB"))
                   (impcons (imp (lmid "modC")) impnil))
                  (dfcons (lid "d")
                   (tmapp (tmabs (lid "a") tynat (tmvar (lid "a"))) (tmnum (lnat "1")))
                   (dfcons (lid "e") (tmnum (lnat "2"))
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
testM05mod = Mod (md (lmid "modA")
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
testM06mod = Mod (md (lmid "modB")
                  (impcons (imp (lmid "modA"))
                   (impcons (imp (lmid "modD"))
                    impnil))
                  (dfcons (lid "a")
                   (tmlet (lid "b") (tmadd (tmvar (lid "d")) (tmnum (lnat "2")))
                              (tmadd (tmvar (lid "b")) (tmnum (lnat "1"))))
                   (dfcons (lid "b") (tmadd (tmvar (lid "a")) (tmnum (lnat "3")))
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
testM07mod = Mod (md (lmid "modC")
               (impcons (imp (lmid "modA"))
                (impcons (imp (lmid "modB"))
                 impnil))
               (dfcons (lid "c") (tmadd (tmnum (lnat "3"))
                                  (tmlet (lid "d") (tmvar (lid "a")) (tmvar (lid "d"))))
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
-- testM08mod :: Mod
-- testM08mod = Mod (md modB
--                   (impcons (imp modA)
--                    impnil)
--                   dfnil)
--              extOr
-- testM08intf :: Intf
-- testM08intf = intf [testM05intf] testM08mod
-- testM08 :: (String, [Intf], Mod)
-- testM08 = ("B: defines or and uses let",
--            [testM05intf],
--            testM08mod)

-- module B
-- import A // defines let extension
-- // define letfun1 extension which uses let
testM09mod :: Mod
testM09mod = Mod (md (lmid "modB")
                  (impcons (imp (lmid "modA"))
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
testM10mod = Mod (md (lmid "modA") impnil dfnil)
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
testM11mod = Mod (md (lmid "modB") impnil dfnil)
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
testM12mod = Mod (md (lmid "modC")
                  (impcons (imp (lmid "modA"))
                   (impcons (imp (lmid "modB"))
                    impnil))
                  dfnil)
             (Ext sdeclsLetstarP aritiesLetstarP infRulesLetstarP [] grdRRsLetstarP)
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
testMR01mod = Mod (md (lmid "modA")
                  impnil
                  dfnil)
              (Ext (sdeclsLet++sdeclsLetNat)
               (aritiesLet++aritiesLetNat)
               (infRulesLet++infRulesLetNat)
               univRRsLetNat grdRRsLet)
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
testC01mod = Mod (md (lmid "modA")
                  (impcons (imp (lmid "modB")) impnil)
                  (dfcons (lid "a")
                   (tmsnd (tmpair (tmnum (lnat "1")) (tmnum (lnat "3"))))
                   (dfcons (lid "b") (tmpair tmtrue tmfalse)
                    (dfcons (lid "c") (tmif (tmsnd (tmvar (lid "b")))
                                            (tmnum (lnat "4")) (tmnum (lnat "2")))
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
testC02mod = Mod (md (lmid "modC")
                  (impcons (imp (lmid "modA")) impnil)
                  (dfcons (lid "d") (tmvar (lid "b"))
                   (dfcons (lid "e") (tmsnd (tmvar (lid "d")))
                    dfnil)))
             extEmpty
testC02 :: (String, [Intf], Mod)
testC02 = ("use module A (with pair)",
           [testC01intf],
           testC02mod)

testC03mod :: Mod
testC03mod = Mod (md (lmid "modD")
                  (impcons (imp (lmid "modA")) impnil)
                  dfnil)
             extLetstarBL
testC03intf :: Intf
testC03intf = intf [testM05intf] testC03mod
testC03 :: (String, [Intf], Mod)
testC03 = ("define let* using imported let",
           [testM05intf],
           testC03mod)

testC04mod :: Mod
testC04mod = Mod (md (lmid "modE")
                  (impcons (imp (lmid "modD")) -- import letstarBL
                   (impcons (imp (lmid "modB")) impnil)) -- import pair
                  (dfcons (lid "e")
                   (tmadd
                    (tmletstarbl (bdgconsbl (lid "a")
                                  (tmpair (tmadd (tmnum (lnat "1")) (tmnum (lnat "2")))
                                              (tmnum (lnat "6")))
                                  (bdgconsbl (lid "b")
                                   (tmfst (tmvar (lid "a")))
                                   (bdgconsbl (lid "c")
                                    (tmsnd (tmvar (lid "a"))) bdgnilbl)))
                     (tmadd (tmvar (lid "b")) (tmvar (lid "c"))))
                    (tmnum (lnat "6")))
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
 -- testX03,
 testX04,
 testX05,
 testX06,
 testX07,
 testX08,
 testX09,
 testX10,
 testX11,
 testX12,
 testX13
 ]

testX01 :: (String, Ext, [a])
testX01 = ("Let",extLet,[])
testX02 :: (String, Ext, [a])
testX02 = ("NatPair",extNatPair,[])
-- testX03 :: (String, Ext, [Ext])
-- testX03 = ("Or",extOr,[extLet])
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
testX13 :: (String, Ext, [a])
testX13 = ("extLetstarP",extLetstarP,[])

-- Rejected extensions

testCasesRejectExtension :: [(String, Ext, [a])]
testCasesRejectExtension = [
 testR01,
 testR02,
 testR03,
 testR04,
 testR05,
-- testR06,
 testR07
 ]

testR01 :: (String, Ext, [a])
testR01 = ("LetWrong1",
           Ext sdeclsLet aritiesLet infRulesLetWrong1 [] grdRRsLetWrong1,
           [])
testR02 :: (String, Ext, [a])
testR02 = ("LetWrong2",
           Ext sdeclsLet aritiesLet infRulesLetWrong2 [] grdRRsLetWrong2,
           [])
testR03 :: (String, Ext, [a])
testR03 = ("LetstarNNWrong",extLetstarNNWrong,[])
testR04 :: (String, Ext, [a])
testR04 = ("LetAnnoWrong1",extLetAnnoWrong1,[])
testR05 :: (String, Ext, [a])
testR05 = ("LetAnnoWrong2",extLetAnnoWrong2,[])
-- testR06 :: (String, Ext, [a])
-- testR06 = ("LetstarPWrong",extLetstarP,[])
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
 -- test15,
 test16,
 test17,
 test18,
 test19,
 test20,
 test21,
 test22,
 test27,
 test28,
 test29,
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
     tj envnil (tmapp (tmabs (lid "a") tybool (tmvar (lid "a"))) tmtrue) tybool)

test02 :: (String, [a], Judg)
test02 =
    ("test02",
     [],
     tj envnil (tmapp (tmabs (lid "a") tybool (tmvar (lid "a"))) tmtrue) vU)

test03 :: (String, [a], Judg)
test03 =
    ("test03",
     [],
     tj (envtm envnil (lid "b") tybool) (tmapp (tmabs (lid "a") tybool (tmvar (lid "b"))) tmtrue) vU)

test04 :: (String, [a], Judg)
test04 =
    ("test04",
     [],
     tj (envtm (envtm (envtm envnil (lid "a") tybool) (lid "b") (tyfun tynat tybool)) (lid "c") tynat)
       (tmvar (lid "b")) vU)

test05 :: (String, [a], Judg)
test05 =
    ("test05",
     [],
     fj (lid "a") (envtm envnil (lid "b") tybool))

test06 :: (String, [Ext], Judg)
test06 =
    ("test06",
     [extLet],
     tj envnil (tmlet (lid "a") (tmnum (lnat "1")) (tmvar (lid "a"))) vU)

test07 :: (String, [Ext], Judg)
test07 =
    ("test07",
     [extLet],
     tj (envtm envnil (lid "a") tybool) (tmlet (lid "a") (tmnum (lnat "5"))
                                         (tmvar (lid "a"))) vU)

test08 :: (String, [Ext], Judg)
test08 =
    ("test08",
     [extLet],
     tj (envtm envnil (lid "b") tynat)
       (tmadd (tmvar (lid "b")) (tmlet (lid "a") (tmnum (lnat "7"))
                                 (tmvar (lid "a")))) vU)

test09 :: (String, [Ext], Judg)
test09 =
    ("test09",
     [extNatPair],
     tj (envtm envnil (lid "a") tynatpair) (tmvar (lid "a")) vU)

test10 :: (String, [Ext], Judg)
test10 =
    ("test10",
     [extNatPair],
     tj envnil (tmnatpair (tmnum (lnat "1")) (tmnum (lnat "2"))) vU)

test10a :: (String, [Ext], Judg)
test10a =
    ("test10a",
     [extNatPair],
     tj (envtm envnil (lid "a") tybool)
     (tmnatpair (tmnum (lnat "1")) (tmnum (lnat "2"))) vU)

test10b :: (String, [Ext], Judg)
test10b =
    ("test10b",
     [extNatPair],
     tj (envtm (envtm envnil (lid "b") tynat) (lid "a") tybool)
     (tmnatpair (tmvar (lid "b")) (tmnum (lnat "4"))) vU)

test10c :: (String, [Ext], Judg)
test10c =
    ("test10c",
     [extNatPair],
     tj (envtm (envtm (envtm envnil (lid "e") (tyfun tynatpair tynat)) (lid "b") tynat)
              (lid "a") tybool)
            (tmapp (tmvar (lid "e")) (tmnatpair (tmvar (lid "b")) (tmnum (lnat "1")))) vU)

test10d :: (String, [Ext], Judg)
test10d =
    ("test10d",
     [extNatPair],
     tj (envtm envnil (lid "a") tybool) (tmabs (lid "a") tynat
                                 (tmnatpair (tmvar (lid "a")) (tmnum (lnat "0")))) vU)

test11 :: (String, [Ext], Judg)
test11 =
    ("test11",
     [extNatPair],
     tj envnil (tmnatsnd (tmnatpair (tmnum (lnat "3")) (tmnum (lnat "5")) )) vU)

test11a :: (String, [Ext], Judg)
test11a =
    ("test11a",
     [extNatPair],
     tj envnil (tmnatsnd (tmnatpair (tmnum (lnat "2")) (tmnum (lnat "1")))) vU)

test12 :: (String, [Ext], Judg)
test12 =
    ("test12",
     [extNatPair],
     tj envnil (tmabs (lid "a") tynat (tmnatpair (tmnum (lnat "1"))
                                       (tmvar (lid "a")))) vU)

test13 :: (String, [Ext], Judg)
test13 =
    ("test13",
     [extNatPair],
     tj envnil (tmnatpair (tmnum (lnat "2")) (tmnum (lnat "6"))) vU)

test14 :: (String, [Ext], Judg)
test14 =
    ("test14",
     [extNatPair,extLet],
     tj envnil (tmlet (lid "a")
                (tmnatpair (tmnum (lnat "2")) (tmnum (lnat "7")))
                (tmnatfst (tmvar (lid "a")))) vU)

-- test15 :: (String, [Ext], Judg)
-- test15 =
--     ("test15",
--      [extOr,extLet],
--      tj (envtm envnil (lid "a") tybool) (tmor tmtrue (tmvar (lid "a"))) vU)

test16 :: (String, [Ext], Judg)
test16 =
    ("test16",
     [extLetFun1,extLet],
     tj envnil (tmletfun1 (lid "a") (lid "b") tynat
                (tmvar (lid "b"))
                (tmapp (tmvar (lid "a")) (tmnum (lnat "8")))) vU)

test17 :: (String, [Ext], Judg)
test17 =
    ("test17",
     [extLetFun1,extLet],
     tj envnil
     (tmadd (tmletfun1 (lid "a") (lid "b") tynat (tmvar (lid "b"))
             (tmapp (tmvar (lid "a")) (tmnum (lnat "3")))) (tmnum (lnat "2")))
      vU)

test18 :: (String, [Ext], Judg)
test18 =
    ("test18",
     [extLetstar],
     tj envnil
     (tmletstar (bdgcons (lid "a") tmtrue (bdgcons (lid "b") (tmvar (lid "a")) bdgnil))
     (tmif (tmvar (lid "b")) (tmnum (lnat "5")) (tmnum (lnat "2"))))
     vU)

-- ∅ ⊢ (let a = true; b = a in if b then n else n) + n : Nat
test19 :: (String, [Ext], Judg)
test19 =
    ("test19",
     [extLetstar],
     tj envnil
     (tmadd (tmletstar (bdgcons (lid "a") tmtrue (bdgcons (lid "b") (tmvar (lid "a")) bdgnil))
      (tmif (tmvar (lid "b")) (tmnum (lnat "1")) (tmnum (lnat "2")))) (tmnum (lnat "3")))
     vU)

test20 :: (String, [Ext], Judg)
test20 =
    ("test20",
     [extLetstar],
     tj envnil
     (tmletstar (bdgcons (lid "a") tmtrue bdgnil)
     (tmif (tmvar (lid "a")) (tmnum (lnat "1")) (tmnum (lnat "2"))))
     vU)

test21 :: (String, [Ext], Judg)
test21 =
    ("test21",
     [extLetstar,extNatPair],
     tj envnil
        (tmletstar (bdgcons (lid "a")
                    (tmnatpair (tmadd (tmnum (lnat "1")) (tmnum (lnat "2")))
                                   (tmnum (lnat "2")))
                    (bdgcons (lid "b") (tmnatfst (tmvar (lid "a")))
                     (bdgcons (lid "c") (tmnatsnd (tmvar (lid "a"))) bdgnil)))
         (tmadd (tmvar (lid "b")) (tmvar (lid "c"))))
        vU)

test22 :: (String, [Ext], Judg)
test22 =
    ("test22",
     [extLetstar,extNatPair],
     tj (envtm envnil (lid "a") tybool)
        (tmadd
         (tmletstar (bdgcons (lid "a") (tmnatpair
                                        (tmadd (tmnum (lnat "1")) (tmnum (lnat "2")))
                                        (tmnum (lnat "4")))
                     (bdgcons (lid "b") (tmnatfst (tmvar (lid "a")))
                      (bdgcons (lid "c") (tmnatsnd (tmvar (lid "a"))) bdgnil)))
          (tmadd (tmvar (lid "b")) (tmvar (lid "c"))))
         (tmnum (lnat "9")))
        vU)

-- Forgotten rewrite rule
-- test23 =
--     ("test23",
--      infRulesNatPair,
--      drop 1 rewRulesNatPair,
--      tj (envtm envnil (lid "a") tynatpair) (tmvar (lid "a")) tynatpair)

-- For (bogus) T-NatPairWeak rule
test24 :: (String, [Ext], Judg)
test24 =
    ("test24",
     [extNatPair],
     tj (envtm (envtm envnil (lid "b") tynat) (lid "a") tybool)
            (tmnatfst (tmnatpair (tmvar (lid "b")) (tmnum (lnat "3")))) vU)
test25 :: (String, [Ext], Judg)
test25 =
    ("test25",
     [extNatPair],
     tj (envtm (envtm envnil (lid "b") tynat) (lid "a") tynatpair)
            (tmnatpair (tmvar (lid "b")) (tmnum (lnat "3"))) vU)
test26 :: (String, [Ext], Judg)
test26 =
    ("test26",
     [extNatPair],
     tj (envtm (envtm envnil (lid "b") tynat) (lid "a") tynatpair)
            (tmnatsnd (tmnatpair (tmnum (lnat "2")) (tmnum (lnat "5")))) vU)

test27 :: (String, [Ext], Judg)
test27 =
    ("test27",
     [extLetstarP],
     tj envnil (tmadd (tmnum (lnat "5"))
                (tmfst (tmpair (tmnum (lnat "2")) (tmnum (lnat "5"))))) vU)

-- This one does not fail during desugaring and
-- the used part of the extension would be accepted
-- by verification
test28 :: (String, [Ext], Judg)
test28 =
    ("test28",
     [extLetstarP],
     tj envnil (tmletstar
                (bdgpair (lid "a") (lid "b")
                 (tmpair (tmnum (lnat "4")) (tmnum (lnat "6")))
                 (bdgcons (lid "c") (tmvar (lid "b")) bdgnil))
                (tmadd (tmnum (lnat "6")) (tmvar (lid "c")))) vU)

-- This one fails during desugaring. But extension is not
-- accepted during verification
test29 :: (String, [Ext], Judg)
test29 =
    ("test29",
     [extLetstarP],
     tj envnil (tmletstar
                (bdgpair (lid "a") (lid "b")
                 (tmpair (tmnum (lnat "4")) (tmnum (lnat "2"))) bdgnil)
                 (tmvar (lid "b"))) vU)

test30 :: (String, [Ext], Judg)
test30 =
    ("test30",
     [extRedefPlusU],
      tj envnil (tmadd (tmnum (lnat "2")) (tmnum (lnat "5"))) vU)

test31 :: (String, [Ext], Judg)
test31 =
    ("test31",
     [extRedefPlusU],
      tj envnil (tmapp (tmabs (lid "a") tynat (tmvar (lid "a")))
                 (tmadd (tmnum (lnat "2")) (tmnum (lnat "5")))) vU)

test32 :: (String, [Ext], Judg)
test32 =
    ("test32",
     [extRedefPlusU],
      tj envnil (tmadd (tmnum (lnat "2")) (tmnum (lnat "5"))) vU)

test33 :: (String, [Ext], Judg)
test33 =
    ("test33",
     [extRedefPlusR],
      tj envnil (tmapp (tmabs (lid "a") tynat (tmvar (lid "a")))
                 (tmadd (tmnum (lnat "2")) (tmnum (lnat "5")))) vU)

test34 :: (String, [Ext], Judg)
test34 =
    ("test34",
     [extLetstar,extPair],
     tj (envtm envnil (lid "a") tybool)
        (tmadd
         (tmletstar (bdgcons (lid "a")
                     (tmpair (tmadd (tmnum (lnat "2")) (tmnum (lnat "5")))
                             (tmnum (lnat "7")))
                     (bdgcons (lid "b") (tmfst (tmvar (lid "a")))
                      (bdgcons (lid "c") (tmsnd (tmvar (lid "a"))) bdgnil)))
          (tmadd (tmvar (lid "b")) (tmvar (lid "c"))))
         (tmnum (lnat "0")))
        vU)

test35 :: (String, [Ext], Judg)
test35 =
    ("test35",
     [extWhere],
     tj envnil
        (tmwhere (tmadd (tmvar (lid "b")) (tmvar (lid "a")))
         (bdgcons (lid "a") (tmnum (lnat "6"))
          (bdgcons (lid "b") (tmvar (lid "a"))
           (bdgcons (lid "c") (tmadd (tmnum (lnat "9")) (tmvar (lid "b")))
            bdgnil))))
     vU)
