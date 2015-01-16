module SimpleTypesExtensions where

import Syntax
import SimpleTypes
import Variables


-- -----------------------------------------------------------------------------
-- Correct extensions
-- -----------------------------------------------------------------------------

-- Let extension

aritiesLet :: [Arity]
aritiesLet = [Arity "let" ["Id","Term","Term"] "Term"]

tmlet :: Expr -> Expr -> Expr -> Expr
tmlet x tm1 tm2 = ECon "let" [x,tm1,tm2]

infRulesLet :: [InfRule]
infRulesLet = [
 InfRule [tj vC vt1 vT1, tj (envtm vC vx vT1) vt2 vT2] "T-Let"
             (tj vC (tmlet vx vt1 vt2) vT2)
 ]

resRRsLet :: [ResRR]
resRRsLet = [
  ResRR [tj vC vt1 vT1, tj (envtm vC vx vT1) vt2 vT2]
        [vC] (tmlet vy vs1 vs2) [vT2] "TJ"
     (tmapp (tmabs vy vT1 vs2) vs1)
 ]

extLet :: Ext
extLet = Ext aritiesLet infRulesLet [] resRRsLet

-- Let nat extension which syntactically overlaps with let

aritiesLetNat :: [Arity]
aritiesLetNat = [Arity "let" ["Id","Term","Term"] "Term"]

tmletNat :: Expr -> Expr -> Expr -> Expr
tmletNat x tm1 tm2 = ECon "let" [x,tm1,tm2]

infRulesLetNat :: [InfRule]
infRulesLetNat = [
 InfRule [tj vC vt1 tynat, tj (envtm vC vx tynat) vt2 vT2] "T-LetNat"
             (tj vC (tmletNat vx vt1 vt2) vT2)
 ]

univRRsLetNat :: [UnivRR]
univRRsLetNat = [
  UnivRR (tmletNat vx vt1 vt2)
         (tmapp (tmabs vx tynat vt2) vt1)
 ]

extLetNat :: Ext
extLetNat = Ext aritiesLetNat infRulesLetNat univRRsLetNat []


-- letstar extension

aritiesLetstar :: [Arity]
aritiesLetstar = [
 Arity "letstar" ["Bindings","Term"] "Term",
 Arity "bdgcons" ["Id","Term","Bindings"] "Bindings",
 Arity "bdgnil" [] "Bindings"
 ]

tmletstar :: Expr -> Expr -> Expr
tmletstar bdg tm = ECon "letstar" [bdg,tm]

bdgcons :: Expr -> Expr -> Expr -> Expr
bdgcons x tm bdg = ECon "bdgcons" [x,tm,bdg]
bdgnil :: Expr
bdgnil = ECon "bdgnil" []

infRulesLetstar :: [InfRule]
infRulesLetstar = [
  InfRule [tj vC vt1 vT1,
           tj (envtm vC vx vT1)
           (tmletstar vBs vt2) vT2] "T-Let*Cons"
          (tj vC (tmletstar (bdgcons vx vt1 vBs) vt2) vT2),
  InfRule [tj vC vt1 vT1, tj (envtm vC vx vT1) vt2 vT2] "T-Let*Last"
              (tj vC (tmletstar (bdgcons vx vt1 bdgnil) vt2) vT2)
 ]

resRRsLetstar :: [ResRR]
resRRsLetstar = [
  ResRR [tj vC vt1 vT1, tj (envtm vC vx vT1)
          (tmletstar vBs vt2) vT2]
        [vC]
          (tmletstar (bdgcons vx vt1 vBs) vt2)
          [vT] "TJ"
    (tmapp (tmabs vx vT1 (tmletstar vBs vt2)) vt1),
  ResRR [tj vC vt1 vT1, tj (envtm vC vx vT1) vt2 vT2]
        [vC] (tmletstar (bdgcons vx vt1 bdgnil) vt2) [vT] "TJ"
    (tmapp (tmabs vx vT1 vt2) vt1)
 ]

extLetstar :: Ext
extLetstar = Ext aritiesLetstar infRulesLetstar [] resRRsLetstar


-- letstar using let extension

aritiesLetstarBL :: [Arity]
aritiesLetstarBL = [
 Arity "letstarbl" ["BindingsBL","Term"] "Term",
 Arity "bdgconsbl" ["Id","Term","BindingsBL"] "BindingsBL",
 Arity "bdgnilbl" [] "BindingsBL"
 ]

tmletstarbl :: Expr -> Expr -> Expr
tmletstarbl bdg tm = ECon "letstarbl" [bdg,tm]

bdgconsbl :: Expr -> Expr -> Expr -> Expr
bdgconsbl x tm bdg = ECon "bdgconsbl" [x,tm,bdg]
bdgnilbl :: Expr
bdgnilbl = ECon "bdgnilbl" []

infRulesLetstarBL :: [InfRule]
infRulesLetstarBL = [
  InfRule [tj vC vt1 vT1,
           tj (envtm vC vx vT1)
           (tmletstarbl vBBLs vt2) vT2] "T-Let*Cons"
          (tj vC (tmletstarbl (bdgconsbl vx vt1 vBBLs) vt2) vT2),
  InfRule [tj vC vt1 vT1, tj (envtm vC vx vT1) vt2 vT2] "T-Let*Last"
              (tj vC (tmletstarbl (bdgconsbl vx vt1 bdgnilbl) vt2) vT2)
 ]

resRRsLetstarBL :: [ResRR]
resRRsLetstarBL = [
  ResRR [tj vC vt1 vT1, tj (envtm vC vx vT1)
          (tmletstarbl vBBLs vt2) vT2]
        [vC]
          (tmletstarbl (bdgconsbl vx vt1 vBBLs) vt2)
          [vT] "TJ"
    (tmlet vx vt1 (tmletstarbl vBBLs vt2)),
    -- (tmapp (tmabs vx vT1 (tmletstar vBs vt2)) vt1),
  ResRR [tj vC vt1 vT1, tj (envtm vC vx vT1) vt2 vT2]
        [vC] (tmletstarbl (bdgconsbl vx vt1 bdgnilbl) vt2) [vT] "TJ"
    (tmlet vx vt1 vt2)
    -- (tmapp (tmabs vx vT1 vt2) vt1)
 ]

extLetstarBL :: Ext
extLetstarBL = Ext aritiesLetstarBL infRulesLetstarBL [] resRRsLetstarBL


-- NatPair extension

aritiesNatPair :: [Arity]
aritiesNatPair = [
 Arity "natpair" ["Term","Term"] "Term",
 Arity "natfst" ["Term"] "Term",
 Arity "natsnd" ["Term"] "Term",
 Arity "NatPair" [] "Type"
 ]

tmnatpair :: Expr -> Expr -> Expr
tmnatpair tm1 tm2 = ECon "natpair" [tm1,tm2]
tmnatfst :: Expr -> Expr
tmnatfst tm = ECon "natfst" [tm]
tmnatsnd :: Expr -> Expr
tmnatsnd tm = ECon "natsnd" [tm]
tynatpair :: Expr
tynatpair = ECon "NatPair" []

infRulesNatPair :: [InfRule]
infRulesNatPair = [
 InfRule [tj (envtm vC evG (tyfun tynat (tyfun tynat tynat))) vt1 tynat,
          tj (envtm vC evG (tyfun tynat (tyfun tynat tynat))) vt2 tynat
         ] "T-NatPair"
         (tj vC (tmnatpair vt1 vt2) tynatpair),
 InfRule [tj vC vt tynatpair,
          fj evG2 vC -- necessary to weaken away variable g2
         ] "T-NatFst"
         (tj vC (tmnatfst vt) tynat),
 InfRule [tj vC vt tynatpair] "T-NatSnd"
         (tj vC (tmnatsnd vt) tynat)
 -- InfRule [fj vz vC, tj vC vt tynatpair, fj vx vC, fj vy (envtm vC vx tynat)] "T-NatSndWeak"
 --         (tj (envtm vC vz vS) (tmnatsnd vt) tynat)-- ,
 -- InfRule [fj vz vC, tj vC vt1 tynat, tj vC vt2 tynat, fj vx vC] "T-NatPairWeak"
 --         (tj (envtm vC vz vS) (tmnatpair vt1 vt2) tynatpair)
 ]

univRRsNatPair :: [UnivRR]
univRRsNatPair = [
 UnivRR tynatpair (tyfun (tyfun tynat (tyfun tynat tynat)) tynat),

 UnivRR (tmnatpair vt1 vt2)
        (tmabs evG (tyfun tynat (tyfun tynat tynat))
         (tmapp (tmapp (tmvar evG) vt1) vt2)),

 UnivRR (tmnatfst vt1)
        (tmapp vt1 (tmabs evG1 tynat (tmabs evG2 tynat (tmvar evG1)))),

 UnivRR (tmnatsnd vt1)
        (tmapp vt1 (tmabs evG1 tynat (tmabs evG2 tynat (tmvar evG2))))
 ]

extNatPair :: Ext
extNatPair = Ext aritiesNatPair infRulesNatPair univRRsNatPair []

-- Or extension

aritiesOr :: [Arity]
aritiesOr = [Arity "or" ["Term","Term"] "Term"]

tmor :: Expr -> Expr -> Expr
tmor tm1 tm2 = ECon "or" [tm1,tm2]

infRulesOr :: [InfRule]
infRulesOr = [
 InfRule [tj vC vt1 tybool, tj vC vt2 tybool, fj vy vC] "T-Or"
         (tj vC (tmor vt1 vt2) tybool)
 ]

resRRsOr :: [ResRR]
resRRsOr = [
  ResRR [tj vC vt1 tybool, tj vC vt2 tybool, fj vy vC]
        [vC] (tmor vt1 vt2) [vT] "TJ"
    (tmlet vy vt1 (tmif (tmvar vy) tmtrue vt2))
 ]

extOr :: Ext
extOr = Ext aritiesOr infRulesOr [] resRRsOr


-- LetFun1 extension
-- let f x = e1 in e1

aritiesLetFun1 :: [Arity]
aritiesLetFun1 = [Arity "letfun1" ["Id","Id","Type","Term","Term"] "Term"]

tmletfun1 :: Expr -> Expr -> Expr -> Expr -> Expr -> Expr
tmletfun1 x y ty tm1 tm2 = ECon "letfun1" [x,y,ty,tm1,tm2]

infRulesLetFun1 :: [InfRule]
infRulesLetFun1 = [
 InfRule [tj (envtm vC vy vT11) vt1 vT12,
          tj (envtm vC vx (tyfun vT11 vT12)) vt2 vT2] "T-LetFun1"
         (tj vC (tmletfun1 vx vy vT11 vt1 vt2) vT2)
 ]

univRRsLetFun1 :: [UnivRR]
univRRsLetFun1 = [
 UnivRR (tmletfun1 vx vy vT11 vt1 vt2)
        (tmlet vx (tmabs vy vT11 vt1) vt2)
 ]

extLetFun1 :: Ext
extLetFun1 = Ext aritiesLetFun1 infRulesLetFun1 univRRsLetFun1 []

-- Bogus extension

-- tmbogus tm1 tm2 = ECon "bogus" [tm1,tm2]

-- -- Cannot be verified. The verifier cannot deduce
-- --    Γ ⊢ t1 : Nat
-- -- from
-- --    Γ ⊢ λx:Nat->Nat->Nat. x t1 : (Nat->Nat->Nat)->Nat
-- -- and
-- --    x ∉ dom(Γ).
-- -- This would require inversion of the typing judgment.
-- -- But since such an extension can easily be rewritten with
-- -- two more natural premises (Γ ⊢ t1 : Nat) and (Γ ⊢ t2 : Nat)
-- -- this is not an issue.
-- infRulesBogus = [
--  InfRule [tj vC (tmnatpair vt1 vt2) tynatpair, fj vx vC] "T-Bogus"
--          (tj vC (tmbogus vt1 vt2) tynat)
--  ]

-- rewRulesBogus = [
--  RewRule (PatJ [vC] (tmbogus vt1 vt2) [vT] "TJ")
--              []
--              (tmadd vt1 vt1)
--  ]


-- Double extension

aritiesDouble :: [Arity]
aritiesDouble = [Arity "double" ["Term"] "Term"]

tmdouble :: Expr -> Expr
tmdouble tm = ECon "double" [tm]

-- The (fj vx vC) premise is unfortunate but the extension is not
-- verified otherwise.
infRulesDouble :: [InfRule]
infRulesDouble = [
 InfRule [tj (envtm vC evG (tyfun tynat (tyfun tynat tynat))) vt tynat
         ] "T-Double"
         (tj vC (tmdouble vt) tynatpair)
 ]

univRRsDouble :: [UnivRR]
univRRsDouble = [
 UnivRR (tmdouble vt1)
               (tmnatpair vt1 vt1)
 ]

extDouble :: Ext
extDouble = Ext aritiesDouble infRulesDouble univRRsDouble []


-- "Polymorhic pairs"

aritiesPair :: [Arity]
aritiesPair = [
 Arity "pair" ["Term","Term"] "Term",
 Arity "fst" ["Term"] "Term",
 Arity "snd" ["Term"] "Term",
 Arity "Pair" ["Type"] "Type"
 ]

tmpair :: Expr -> Expr -> Expr
tmpair tm1 tm2 = ECon "pair" [tm1,tm2]
tmfst :: Expr -> Expr
tmfst tm = ECon "fst" [tm]
tmsnd :: Expr -> Expr
tmsnd tm = ECon "snd" [tm]
typair :: Expr -> Expr
typair ty = ECon "Pair" [ty]

infRulesPair :: [InfRule]
infRulesPair = [
 InfRule [tj (envtm vC evG (tyfun vT (tyfun vT vT))) vt1 vT,
          tj (envtm vC evG (tyfun vT (tyfun vT vT))) vt2 vT
         ] "T-Pair"
         (tj vC (tmpair vt1 vt2) (typair vT)),
 InfRule [tj vC vt (typair vT),
          fj evG2 vC -- necessary to weaken away variable g2
         ] "T-Fst"
         (tj vC (tmfst vt) vT),
 InfRule [tj vC vt (typair vT)] "T-Snd"
         (tj vC (tmsnd vt) vT)
 ]

univRRsPair :: [UnivRR]
univRRsPair = [
 UnivRR (typair vT) (tyfun (tyfun vT (tyfun vT vT)) vT)
 ]

resRRsPair :: [ResRR]
resRRsPair = [
 ResRR [tj (envtm vC evG (tyfun vT (tyfun vT vT))) vt1 vT,
        tj (envtm vC evG (tyfun vT (tyfun vT vT))) vt2 vT]
       [vC] (tmpair vt1 vt2) [vS] "TJ" -- [typair vT] -- see [Note 1]
   (tmabs evG (tyfun vT (tyfun vT vT))
    (tmapp (tmapp (tmvar evG) vt1) vt2)),
 ResRR [tj vC vt vS, --(typair vT), -- see [Note 1]
       fj evG2 vC]
       [vC] (tmfst vt) [vT] "TJ"
   (tmapp vt (tmabs evG1 vT (tmabs evG2 vT (tmvar evG1)))),
 ResRR [tj vC vt vS] --(typair vT)] -- see [Note 1]
       [vC] (tmsnd vt) [vT] "TJ"
   (tmapp vt (tmabs evG1 vT (tmabs evG2 vT (tmvar evG2))))
 ]

extPair :: Ext
extPair = Ext aritiesPair infRulesPair univRRsPair resRRsPair

-- Pattern matching for pairs in let*

aritiesLetstarP :: [Arity]
aritiesLetstarP = [
 Arity "bdgpair" ["Id","Id","Term","Bindings"] "Bindings"
 ]

bdgpair :: Expr -> Expr -> Expr -> Expr -> Expr
bdgpair x y tm bdg = ECon "bdgpair" [x,y,tm,bdg]

infRulesLetstarP :: [InfRule]
infRulesLetstarP = [
  InfRule [tj vC vt1 (typair vT1),
           fj evG2 vC,
           tj (envtm (envtm vC vx vT1) vy vT1)
           (tmletstar vBs vt2) vT2] "T-Let*PCons"
          (tj vC (tmletstar (bdgpair vx vy vt1 vBs) vt2) vT2),
  InfRule [tj vC vt1 (typair vT1),
           fj evG2 vC,
           tj (envtm (envtm vC vx vT1) vy vT1) vt2 vT2] "T-Let*PLast"
          (tj vC (tmletstar (bdgpair vx vy vt1 bdgnil) vt2) vT2)
 ]

resRRsLetstarP :: [ResRR]
resRRsLetstarP = [
  ResRR [tj vC vt1 (typair vT1), fj evG2 vC, tj (envtm (envtm vC vx vT1) vy vT1)
          (tmletstar vBs vt2) vT2]
        [vC]
          (tmletstar (bdgpair vx vy vt1 vBs) vt2)
          [vT] "TJ"
    (tmapp
     (tmapp
      (tmabs vx vT1 (tmabs vy vT1 (tmletstar vBs vt2)))
       (tmfst vt1))
     (tmsnd vt1)),
  ResRR [tj vC vt1 (typair vT1), fj evG2 vC, tj (envtm (envtm vC vx vT1) vy vT1) vt2 vT2]
        [vC] (tmletstar (bdgpair vx vy vt1 bdgnil) vt2) [vT] "TJ"
    (tmapp (tmapp (tmabs vx vT1 (tmabs vy vT1 vt2)) (tmfst vt1)) (tmsnd vt1))
 ]

extLetstarP :: Ext
extLetstarP = Ext (aritiesLetstar ++ aritiesLetstarP ++ aritiesPair)
              (infRulesLetstar ++ infRulesLetstarP ++ infRulesPair)
              univRRsPair
              (resRRsLetstar ++ resRRsLetstarP ++ resRRsPair)


-- where with multiple bindings using letstar in _one_ extension
aritiesWhere :: [Arity]
aritiesWhere = [
 Arity "where" ["Term","Bindings"] "Term"
 ]

tmwhere :: Expr -> Expr -> Expr
tmwhere tm bdgs = ECon "where" [tm,bdgs]

infRulesWhere :: [InfRule]
infRulesWhere = [
  InfRule [tj vC vt1 vT1,
           tj (envtm vC vx vT1)
           (tmwhere vt2 vBs) vT2] "T-Where*Cons"
          (tj vC (tmwhere vt2 (bdgcons vx vt1 vBs)) vT2),
  InfRule [tj vC vt1 vT1, tj (envtm vC vx vT1) vt2 vT2] "T-Where*Last"
              (tj vC (tmwhere vt2 (bdgcons vx vt1 bdgnil)) vT2)
 ]

univRRsWhere :: [UnivRR]
univRRsWhere = [
  UnivRR (tmwhere vt vBs) (tmletstar vBs vt)
 ]

extWhere :: Ext
extWhere = Ext (aritiesWhere++aritiesLetstar) (infRulesWhere++infRulesLetstar)
    univRRsWhere resRRsLetstar

-- -----------------------------------------------------------------------------
-- Wrong extensions
-- -----------------------------------------------------------------------------

infRulesLetWrong1 :: [InfRule]
infRulesLetWrong1 = [
 InfRule [tj vC vt1 vT1, tj (envtm vC vx vT1) vt2 vT2] "T-Let"
             (tj vC (tmlet vx vt1 vt2) vT2)
 ]

resRRsLetWrong1 :: [ResRR]
resRRsLetWrong1 = [
  ResRR [tj vC vt1 vT1, tj (envtm vC vx vT1) vt2 vT2]
        [vC] (tmlet vx vt1 vt2) [vT2] "TJ"
      (tmapp (tmabs vx vT1 vt1) vt2) -- vt1 and vt2 swapped
 ]

infRulesLetWrong2 :: [InfRule]
infRulesLetWrong2 = [
  InfRule [tj vC vt1 vT1, tj (envtm vC vx vT2) vt2 vT2] "T-Let" -- must be vT1 for
             (tj vC (tmlet vx vt1 vt2) vT2)                   -- vx in environment
 ]

resRRsLetWrong2 :: [ResRR]
resRRsLetWrong2 = [
  ResRR [tj vC vt1 vT1, tj (envtm vC vx vT2) vt2 vT2]
        [vC] (tmlet vx vt1 vt2) [vT2] "TJ"
    (tmapp (tmabs vx vT1 vt2) vt1)
 ]

infRulesLetWrong3 :: [InfRule]
infRulesLetWrong3 = [
  InfRule [tj vC vt1 vT1, tj vC vt2 vT2] "T-Let" -- (envtm vC vx vT1) missing
             (tj vC (tmlet vx vt1 vt2) vT2)
 ]

resRRsLetWrong3 :: [ResRR]
resRRsLetWrong3 = [
  ResRR [tj vC vt1 vT1, tj vC vt2 vT2]
        [vC] (tmlet vx vt1 vt2) [vT2] "TJ"
    (tmapp (tmabs vx vT1 vt2) vt1)
 ]


aritiesLetAnnoWrong :: [Arity]
aritiesLetAnnoWrong = [Arity "letanno" ["Id","Type,","Term","Term"] "Term"]

tmletanno :: Expr -> Expr -> Expr -> Expr -> Expr
tmletanno x ty tm1 tm2 = ECon "letanno" [x,ty,tm1,tm2]

infRulesLetAnnoWrong1 :: [InfRule]
infRulesLetAnnoWrong1 = [
 InfRule [tj vC vt1 vT1, tj (envtm vC vx vT1) vt2 vT2] "T-Let"
             (tj vC (tmletanno vx vT1 vt1 vt2) vT2)
 ]

univRRsLetAnnoWrong1 :: [UnivRR]
univRRsLetAnnoWrong1 = [
  UnivRR (tmletanno vx vT1 vt1 vt2)
         (tmapp (tmabs vx vT2 vt2) vt1) -- must be vT1
 ]

extLetAnnoWrong1 :: Ext
extLetAnnoWrong1 = Ext aritiesLetAnnoWrong
                   infRulesLetAnnoWrong1
                   univRRsLetAnnoWrong1
                   []

infRulesLetAnnoWrong2 :: [InfRule]
infRulesLetAnnoWrong2 = [
 InfRule [tj vC vt1 vT, tj (envtm vC vx vT1) vt2 vT2] "T-Let" -- must be vT1 in
             (tj vC (tmletanno vx vT1 vt1 vt2) vT2)          -- first premise
 ]

univRRsLetAnnoWrong2 :: [UnivRR]
univRRsLetAnnoWrong2 = [
  UnivRR (tmletanno vx vT1 vt1 vt2)
         (tmapp (tmabs vx vT2 vt2) vt1)
 ]

extLetAnnoWrong2 :: Ext
extLetAnnoWrong2 = Ext aritiesLetAnnoWrong
                   infRulesLetAnnoWrong2
                   univRRsLetAnnoWrong2
                   []


aritiesLetstarNN :: [Arity]
aritiesLetstarNN = [
 Arity "letstarNN" ["BindingsNN","Term"] "Term",
 Arity "bdgconsNN" ["Id","Id","Term","BindingsNN"] "BindingsNN",
 Arity "bdgnilNN" [] "BindingsNN"
 ]

tmletstarNN :: Expr -> Expr -> Expr
tmletstarNN bdg tm = ECon "letstarNN" [bdg,tm]

bdgconsNN :: Expr -> Expr -> Expr -> Expr -> Expr
bdgconsNN x y tm bdg = ECon "bdgconsNN" [x,y,tm,bdg]
bdgnilNN :: Expr
bdgnilNN = ECon "bdgnilNN" []

infRulesLetstarNN :: [InfRule]
infRulesLetstarNN = [
 InfRule [tj vC vt1 tynatpair,
          fj evG2 vC,
          tj (envtm (envtm vC vx1 tynat) vx2 tynat)
          (tmletstarNN (bdgconsNN vy1 vy2 vs1 vBs) vt2) vT2] "T-LetNN*Cons"
         (tj vC (tmletstarNN (bdgconsNN vx1 vx2 vt1
                              (bdgconsNN vy1 vy2 vs1 vBs)) vt2) vT2),
 InfRule [tj vC vt1 tynatpair,
          fj evG2 vC,
          tj (envtm (envtm vC vx1 tynat) vx2 tynat) vt2 vT2] "T-LetNN*Last"
             (tj vC (tmletstarNN (bdgconsNN vx1 vx2 vt1 bdgnilNN) vt2) vT2)
 ]

univRRsLetstarNN :: [UnivRR]
univRRsLetstarNN = [
  UnivRR (tmletstarNN (bdgconsNN vx1 vx2 vt1 (bdgconsNN vy1 vy2 vs1 vBs)) vt2)
         (tmapp
          (tmapp
           (tmabs vx1 tynat
            (tmabs vx2 tynat
             (tmletstarNN (bdgconsNN vy1 vy2 vs1 vBs) vt2)))
           (tmnatfst vt1))
          (tmnatsnd vt1)),
  UnivRR (tmletstarNN (bdgconsNN vx1 vx2 vt1 bdgnilNN) vt2)
         (tmapp
          (tmapp
           (tmabs vx1 tynat (tmabs vx2 tynat vt2))
           (tmnatfst vt1))
          (tmnatsnd vt1))
 ]

extLetstarNNWrong :: Ext
extLetstarNNWrong = Ext
               (aritiesLetstarNN++aritiesNatPair)
               (infRulesLetstarNN++infRulesNatPair)
               (univRRsLetstarNN++univRRsNatPair)
               []

extLetstarNNValid :: Ext
extLetstarNNValid =
    Ext aritiesLetstarNN infRulesLetstarNN univRRsLetstarNN []


-- Redefine plus with universal desugaring
univRRsRedefPlusU :: [UnivRR]
univRRsRedefPlusU = [
  UnivRR (tmadd vt1 vt2) vt1
 ]
extRedefPlusU :: Ext
extRedefPlusU = Ext [] [] univRRsRedefPlusU []

-- Redefine plus with restricted desugaring
resRRsRedefPlusR :: [ResRR]
resRRsRedefPlusR = [
  ResRR [tj vC vt1 tynat, tj vC vt2 tynat]
        [vC] (tmadd vt1 vt2) [tynat] "TJ"
        vt1
 ]
extRedefPlusR :: Ext
extRedefPlusR = Ext [] [] [] resRRsRedefPlusR


-- ~~~ Note 1 ~~~
-- If the vS in the three restricted desugarings
-- below are replaced by the commented version (which stem
-- from the typing rules, the order in which the (univ. and restr.)
-- desugarings are applied is not irrelevant anymore. It only works
-- if the restricted are applied prior to the universal ones. The good
-- thing is that verification already detects this. The problem is
-- that the lhs of the restr. des. has `typair vT' in it which is
-- replaced by `tyfun vT ...' by the univ. des. Hence, the lhs does
-- not fit anymore. Fortunately, we can rewrite the lhs since these
-- positions are irrelevant for the right-hand side.
