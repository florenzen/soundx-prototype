module SystemF where

import Syntax
import Variables

-- Base system: ->, bool, nat, ∀

tj env tm ty = Judg [env,tm,ty] "TJ"
fj x env = Judg [x,env] "FJ"
sj env ty1 x ty2 ty3 = Judg [env,ty1,x,ty2,ty3] "SJ"

envnil = ECon "∅" []
envtm env x ty = ECon "envtm" [env,x,ty]
envty env x = ECon "envty" [env,x]

tmvar x = ECon "var" [x]
tmapp tm1 tm2 = ECon "app" [tm1,tm2]
tmabs x ty tm = ECon "abs" [x,ty,tm]
tmtrue = ECon "true" []
tmfalse = ECon "false" []
tmif tm1 tm2 tm3 = ECon "if" [tm1,tm2,tm3]
tmnum = ECon "num" []
tmadd tm1 tm2 = ECon "add" [tm1,tm2]
tmtabs x tm = ECon "tabs" [x,tm]
tmtapp tm ty = ECon "tapp" [tm,ty]

tyvar x = ECon "Var" [x]
tynat = ECon "Nat" []
tybool = ECon "Bool" []
tyfun ty1 ty2 = ECon "Fun" [ty1,ty2]
tyforall x ty = ECon "Forall" [x,ty]

infRuleListSJ = [
 -- Γ ⊢ T = [X->T]X
 InfRule [] "S-Var" (sj vC vT vx vT (tyvar vx)),
 -- Γ ⊢ Y = [X->T]Y
 InfRule [neq vx vy] "S-OtherVar" (sj vC (tyvar vy) vx vT (tyvar vy)),
 -- Γ ⊢ Nat = [X->T]Nat
 InfRule [] "S-Nat" (sj vC tynat vx vT tynat),
 -- Γ ⊢ Bool = [X->T]Bool
 InfRule [] "S-Bool" (sj vC tybool vx vT tybool),
 -- Γ ⊢ U1->U2 = [X->T](S1->S2) where Γ ⊢ U1 = [X->T]S1, Γ ⊢ U2 = [X->T]S2
 InfRule [sj vC vU1 vx vT vS1, sj vC vU2 vx vT vS2] "S-Fun"
             (sj vC (tyfun vU1 vU2) vx vT (tyfun vS1 vS2)),

 InfRule [] "S-Forall1" (sj vC (tyforall vx vS) vx vT (tyforall vx vS)),

 InfRule [fj vy vC, sj (envty vC vy) vU vx vT vS] "S-Forall2"
             (sj vC (tyforall vy vU) vx vT (tyforall vy vS)),

 -- Γ ⊢ ∀Z.U = [X->T](∀Y.S) where
 -- Z∉dom(Γ,Y), Γ,Y,Z ⊢ U1=[Y->Z](S), Γ,Y,Z ⊢ U=[Z->T](U1)
 InfRule
   [fj vz (envty vC vy),
    sj (envty (envty vC vy) vz) vU1 vy (tyvar vz) vS,
    sj (envty (envty vC vy) vz) vU vx vT vU1
   ] "S-Forall3"
   (sj vC (tyforall vz vU) vx vT (tyforall vy vS)),

 -- This is necessary to verify Pair extension which
 -- introduces fresh variables in a forall type that
 -- are substituted in a tapp. Without this rule
 -- the substitution judgment cannot be derived since nothing is known
 -- about vS. This corresponds a little to the weakening rules.
 InfRule [fj vx vC] "S-Fresh" (sj vC vS vx vT vS)
 ]

infRuleListFJ = [
 InfRule [] "F-Empty" (fj vx envnil),
 InfRule [neq vx vy, fj vx vC] "F-TmVar" (fj vx (envtm vC vy vT)),
 InfRule [neq vx vy, fj vx vC] "F-TyVar" (fj vx (envty vC vy))
 ]

-- Γ ⊢ t : T
infRuleListTJ = [
 InfRule [] "T-Var" (tj (envtm vC vx vT) (tmvar vx) vT),
 InfRule [] "T-True" (tj vC tmtrue tybool),
 InfRule [] "T-False" (tj vC tmfalse tybool),
 InfRule [tj vC vt1 tybool, tj vC vt2 vT, tj vC vt3 vT] "T-If"
         (tj vC (tmif vt1 vt2 vt3) vT),
 InfRule [] "T-Nat" (tj vC tmnum tynat),
 InfRule [tj (envtm vC vx vT1) vt vT2] "T-Abs"
   (tj vC (tmabs vx vT1 vt) (tyfun vT1 vT2)),
 InfRule [tj vC vt1 (tyfun vT1 vT2), tj vC vt2 vT1] "T-App"
   (tj vC (tmapp vt1 vt2) vT2),
 InfRule [fj vx vC,
          tj vC vt vT] "T-WeakTm"
          (tj (envtm vC vx vS) vt vT),
 InfRule [fj vx vC,
          tj vC vt vT] "T-WeakTy"
          (tj (envty vC vx) vt vT),
 InfRule [tj vC vt1 tynat, tj vC vt2 tynat] "T-Add"
   (tj vC (tmadd vt1 vt2) tynat),
 InfRule [tj (envty vC vx) vt vT] "T-TAbs"
   (tj vC (tmtabs vx vt) (tyforall vx vT)),
 InfRule [tj vC vt (tyforall vx vS), sj vC vU vx vT vS
         ] "T-TApp"
   (tj vC (tmtapp vt vT) vU)
 ]

infRuleListSF = infRuleListFJ ++ infRuleListTJ ++ infRuleListSJ ++ infRuleListNeq
