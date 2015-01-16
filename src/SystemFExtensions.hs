module SystemFExtensions where

import Variables
import SystemF
import Syntax


-- Pair extension

typair ty1 ty2 = ECon "Pair" [ty1,ty2]
tmpair tm1 tm2 = ECon "pair" [tm1,tm2]
tmfst tm = ECon "fst" [tm]
tmsnd tm = ECon "snd" [tm]

infRuleListPair = [
  InfRule [tj vC vt1 vT1,
           tj vC vt2 vT2,
           fj vz vC,
           fj vy (envty vC vz)
          ] "T-Pair"
          (tj vC (tmpair vt1 vt2) (typair vT1 vT2)),
  InfRule [tj vC vt (typair vT1 vT2),
           fj vx vC,
           fj vy (envtm vC vx vT1)
          ] "T-Fst"
          (tj vC (tmfst vt) vT1),
  InfRule [tj vC vt (typair vT1 vT2),
           fj vx vC,
           fj vy (envtm vC vx vT1)
          ] "T-Snd"
          (tj vC (tmsnd vt) vT2),
  InfRule [sj (envty vC vz) vU1 vx vT vS1,
           sj (envty vC vz) vU2 vx vT vS2,
           fj vz vC, fj vx (envty vC vz)
          ] "S-Pair"
          (sj vC (typair vU1 vU2) vx vT (typair vS1 vS2))
 ]

rewRuleListPair = [
  -- Typing
  RewRule (PatJ [] (PECtx (Var "C") (typair vT1 vT2)) [vt,vT] "TJ")
          [fj vz vC]
          (tyforall vz (tyfun (tyfun vT1 (tyfun vT2 (tyvar vz))) (tyvar vz))),

  RewRule (PatJ [vC] (PECtx (Var "t") (typair vT1 vT2)) [vT] "TJ")
          [fj vz vC]
          (tyforall vz (tyfun (tyfun vT1 (tyfun vT2 (tyvar vz))) (tyvar vz))),

  RewRule (PatJ [vC,vt] (PECtx (Var "T") (typair vT1 vT2)) [] "TJ")
          [fj vz vC]
          (tyforall vz (tyfun (tyfun vT1 (tyfun vT2 (tyvar vz))) (tyvar vz))),


  -- Free in ctx
  RewRule (PatJ [vx] (PECtx (Var "C") (typair vT1 vT2)) [] "FJ")
          [fj vz vC]
          (tyforall vz (tyfun (tyfun vT1 (tyfun vT2 (tyvar vz))) (tyvar vz))),


  -- Substitution (vC vU vx vT vS)
  RewRule (PatJ [] (PECtx (Var "C") (typair vT1 vT2)) [vU,vx,vT,vS] "SJ")
          [fj vz vC]
          (tyforall vz (tyfun (tyfun vT1 (tyfun vT2 (tyvar vz))) (tyvar vz))),

  RewRule (PatJ [vC] (PECtx (Var "U") (typair vT1 vT2)) [vx,vT,vS] "SJ")
          [fj vz vC]
          (tyforall vz (tyfun (tyfun vT1 (tyfun vT2 (tyvar vz))) (tyvar vz))),

  RewRule (PatJ [vC,vU,vx] (PECtx (Var "T") (typair vT1 vT2)) [vS] "SJ")
          [fj vz vC]
          (tyforall vz (tyfun (tyfun vT1 (tyfun vT2 (tyvar vz))) (tyvar vz))),

  RewRule (PatJ [vC,vU,vx,vT] (PECtx (Var "S") (typair vT1 vT2)) [] "SJ")
          [fj vz vC]
          (tyforall vz (tyfun (tyfun vT1 (tyfun vT2 (tyvar vz))) (tyvar vz))),

  -- Terms
  RewRule (PatJ [vC] (PEExpr (tmpair vt1 vt2)) [vT] "TJ")
          [tj vC vt1 vT1, tj vC vt2 vT2, fj vz vC, fj vy (envty vC vz)]
          (tmtabs vz (tmabs vy
                      (tyfun vT1 (tyfun vT2 (tyvar vz)))
                      (tmapp (tmapp (tmvar vy) vt1) vt2))),

  RewRule (PatJ [vC] (PEExpr (tmfst vt)) [vT] "TJ")
          [tj vC vt (typair vT1 vT2), fj vx vC, fj vy (envtm vC vx vT1)]
          (tmapp (tmtapp vt vT1) (tmabs vx vT1 (tmabs vy vT2 (tmvar vx)))),

  RewRule (PatJ [vC] (PEExpr (tmsnd vt)) [vT] "TJ")
          [tj vC vt (typair vT1 vT2), fj vx vC, fj vy (envtm vC vx vT1)]
          (tmapp (tmtapp vt vT2) (tmabs vx vT1 (tmabs vy vT2 (tmvar vy))))
 ]


-- Other cool extensions: lists, list comprehensions


-- Letstar only for natpairs

-- This leads the verifier into a loop. Should be investigated.

tmletstarnn bdg tm = ECon "let*nn" [bdg,tm]

bdgconsnn x tm bdg = ECon "bdgconsnn" [x,tm,bdg]
bdgnilnn = ECon "bdgnilnn" []

infRuleListLetstarNN = [
 InfRule [tj (envtm vC vx (typair tynat tynat))
             (tmletstarnn (bdgconsnn vy vs1 vBs) vt2) vT2,
          tj vC vt1 (typair tynat tynat)
         ] "T-Let*ConsNN"
         (tj vC (tmletstarnn (bdgconsnn vx vt1 (bdgconsnn vy vs1 vBs)) vt2) vT2),
 InfRule [tj vC vt1 (typair tynat tynat),
          tj (envtm vC vx (typair tynat tynat)) vt2 vT2
         ] "T-Let*LastNN"
         (tj vC (tmletstarnn (bdgconsnn vx vt1 bdgnilnn) vt2) vT2)
 ]

rewRuleListLetstarNN = [
 RewRule (PatJ [vC]
          (PEExpr (tmletstarnn (bdgconsnn vx vt1 (bdgconsnn vy vs1 vBs)) vt2))
          [vT] "TJ")
         []
         (tmapp (tmabs vx (typair tynat tynat)
                 (tmletstarnn (bdgconsnn vy vs1 vBs) vt2)) vt1),
 RewRule (PatJ [vC] (PEExpr (tmletstarnn (bdgconsnn vx vt1 bdgnilnn) vt2)) [vT] "TJ")
         []
         (tmapp (tmabs vx (typair tynat tynat) vt2) vt1)
 ]
