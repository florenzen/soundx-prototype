module SimpleTypes where

import Prelude hiding (mod)

import Syntax
import Variables


-- Base system: ->, bool, nat

sdeclsST :: [SortDecl]
sdeclsST = [
 SortDecl "ID" Lexical,
 SortDecl "NAT" Lexical,
 SortDecl "MID" Lexical,
 SortDecl "Term" ContextFree,
 SortDecl "Type" ContextFree,
 SortDecl "Env" ContextFree,
 SortDecl "Ids" ContextFree,
 SortDecl "Defs" ContextFree,
 SortDecl "Module" ContextFree,
 SortDecl "Imports" ContextFree,
 SortDecl "Import" ContextFree,
 SortDecl "Rep" ContextFree
 ]
aritiesST :: [Arity]
aritiesST = [
 Arity "∅" [] "Env",
 Arity "envtm" ["Env","ID","Type"] "Env",
 Arity "var" ["ID"] "Term",
 Arity "app" ["Term","Term"] "Term",
 Arity "abs" ["ID","Type","Term"] "Term",
 Arity "true" [] "Term",
 Arity "false" [] "Term",
 Arity "if" ["Term","Term","Term"] "Term",
 Arity "num" ["NAT"] "Term",
 Arity "add" ["Term","Term"] "Term",
 Arity "Nat" [] "Type",
 Arity "Bool" [] "Type",
 Arity "Fun" ["Type","Type"] "Type",

 Arity "DefNil" [] "Defs",
 Arity "DefCons" ["ID","Term","Defs"] "Defs",

 Arity "IdNil" [] "Ids",
 Arity "IdCons" ["ID","Ids"] "Ids",

 Arity "Module" ["MID","Imports","Defs"] "Module",
 Arity "ImportNil" [] "Imports",
 Arity "ImportCons" ["Import","Imports"] "Imports",
 Arity "Import" ["MID"] "Import",
 Arity "ImportOnly" ["MID", "Ids"] "Import",

 Arity "RepCons" ["MID","Env","Rep"] "Rep",
 Arity "RepNil" [] "Rep"
 ]

formsST :: [Form]
formsST = [
 Form "FJ" ["ID","Env"],
 Form "TJ" ["Env","Term","Type"],
 Form "SJ" ["Rep","Module","Env"],
 Form "UJ" ["Env","Env","Env"],
 Form "RJ" ["Env","Ids","Env"],
 Form "MJ" ["ID","Ids"],
 Form "NJ" ["ID","Ids"],
 Form "IJ" ["Rep","Imports","Env"],
 Form "DJ" ["Env","Defs","Env"],
 Form "LJ" ["MID","Env","Rep"]
 ]

baseST :: Base
baseST = Base sdeclsST aritiesST formsST infRulesST
         "Env" "MID" "Imports" "Import" "Module" "Rep"
         "Module" "ImportNil" "ImportCons" ["Import","ImportOnly"]
         "RepNil" "RepCons"
         "SJ"

tj :: Expr -> Expr -> Expr -> Judg
tj env tm ty = Judg [env,tm,ty] "TJ"
fj :: Expr -> Expr -> Judg
fj x env = Judg [x,env] "FJ"
sj :: Expr -> Expr -> Expr -> Judg
sj rep mod env = Judg [rep,mod,env] "SJ"
uj :: Expr -> Expr -> Expr -> Judg
uj env1 env2 env3 = Judg [env1,env2,env3] "UJ"
rj :: Expr -> Expr -> Expr -> Judg
rj env1 xs env2 = Judg [env1,xs,env2] "RJ"
mj :: Expr -> Expr -> Judg
mj x xs = Judg [x,xs] "MJ"
nj :: Expr -> Expr -> Judg
nj x xs = Judg [x,xs] "NJ"
ij :: Expr -> Expr -> Expr -> Judg
ij rep imps env = Judg [rep,imps,env] "IJ"
lj :: Expr -> Expr -> Expr -> Judg
lj mid sig rep = Judg [mid,sig,rep] "LJ"
dj :: Expr -> Expr -> Expr -> Judg
dj env1 dfs env2 = Judg [env1,dfs,env2] "DJ"

envnil :: Expr
envnil = ECon "∅" []
envtm :: Expr -> Expr -> Expr -> Expr
envtm env x ty = ECon "envtm" [env,x,ty]

tmvar :: Expr -> Expr
tmvar x = ECon "var" [x]
tmapp :: Expr -> Expr -> Expr
tmapp tm1 tm2 = ECon "app" [tm1,tm2]
tmabs :: Expr -> Expr -> Expr -> Expr
tmabs x ty tm = ECon "abs" [x,ty,tm]
tmtrue :: Expr
tmtrue = ECon "true" []
tmfalse :: Expr
tmfalse = ECon "false" []
tmif :: Expr -> Expr -> Expr -> Expr
tmif tm1 tm2 tm3 = ECon "if" [tm1,tm2,tm3]
tmnum :: Expr -> Expr
tmnum n = ECon "num" [n]
tmadd :: Expr -> Expr -> Expr
tmadd tm1 tm2 = ECon "add" [tm1,tm2]

tynat :: Expr
tynat = ECon "Nat" []
tybool :: Expr
tybool = ECon "Bool" []
tyfun :: Expr -> Expr -> Expr
tyfun ty1 ty2 = ECon "Fun" [ty1,ty2]

dfnil :: Expr
dfnil = ECon "DefNil" []
dfcons :: Expr -> Expr -> Expr -> Expr
dfcons x tm dfs = ECon "DefCons" [x,tm,dfs]

idnil :: Expr
idnil = ECon "IdNil" []
idcons :: Expr -> Expr -> Expr
idcons x xs = ECon "IdCons" [x,xs]

md :: Expr -> Expr -> Expr -> Expr
md mid imps dfs = ECon "Module" [mid,imps,dfs]

impnil :: Expr
impnil = ECon "ImportNil" []
impcons :: Expr -> Expr -> Expr
impcons im ims = ECon "ImportCons" [im,ims]
imp :: Expr -> Expr
imp mid = ECon "Import" [mid]
imponly :: Expr -> Expr -> Expr
imponly mid xs = ECon "ImportOnly" [mid,xs]

repcons :: Expr -> Expr -> Expr -> Expr
repcons mid sig rep = ECon "RepCons" [mid,sig,rep]
repnil :: Expr
repnil = ECon "RepNil" []

infRulesFJ :: [InfRule]
infRulesFJ = [
 InfRule [] "F-Empty" (fj vx envnil),
 InfRule [Neq vx vy, fj vx vC] "F-TmVar" (fj vx (envtm vC vy vT))
 ]

infRulesTJ :: [InfRule]
infRulesTJ = [
 InfRule [] "T-Var" (tj (envtm vC vx vT) (tmvar vx) vT),
 InfRule [Neq vx vy, tj vC (tmvar vx) vT] "T-Var1" (tj (envtm vC vy vS) (tmvar vx) vT),
 InfRule [] "T-True" (tj vC tmtrue tybool),
 InfRule [] "T-False" (tj vC tmfalse tybool),
 InfRule [tj vC vt1 tybool, tj vC vt2 vT, tj vC vt3 vT] "T-If"
         (tj vC (tmif vt1 vt2 vt3) vT),
 InfRule [] "T-Nat" (tj vC (tmnum vn) tynat),
 InfRule [tj (envtm vC vx vT1) vt vT2] "T-Abs"
   (tj vC (tmabs vx vT1 vt) (tyfun vT1 vT2)),
 InfRule [tj vC vt1 (tyfun vT1 vT2), tj vC vt2 vT1] "T-App"
   (tj vC (tmapp vt1 vt2) vT2),
 -- InfRule [fj vx vC,
 --          tj vC vt vT] "T-Weak1"
 --          (tj (envtm vC vx vS) vt vT),
 InfRule [tj vC vt1 tynat, tj vC vt2 tynat] "T-Add"
   (tj vC (tmadd vt1 vt2) tynat)
 ]


infRulesMod :: [InfRule]
infRulesMod = [
 -- LJ (lookup judgment)
 -- L-Next:
 --   (mid ≠ mid1) (mid:Γ ∈ rep)
 --   ---------------------------
 --   mid:Γ ∈ mid1:Γ1,rep
 -- L-Found:
 --   -----------------
 --   mid:Γ ∈ mid:Γ,rep
 InfRule [Neq vmid vmid1, lj vmid vC vrep]
         "L-Next"
         (lj vmid vC (repcons vmid1 vC1 vrep)),
 InfRule [] "L-Found"
         (lj vmid vC (repcons vmid vC vrep)),
 -- UJ (union judgment)
 -- U-Empty:
 --   ---------
 --   Γ ⊕ ∅ = Γ
 -- U-Add:
 --   (Γ ⊕ Δ = Γ1) (x∉dom(Γ1))
 --   ------------------------
 --   Γ ⊕ (Δ,x:T) = (Γ1,x:T)
 InfRule [] "U-Empty" (uj vC envnil vC),
 InfRule [uj vC vCD vC1,
          fj vx vC1
         ]
       "U-Add"
         (uj vC (envtm vCD vx vT) (envtm vC1 vx vT)),

 -- RJ (restriction judgment)
 -- R-Empty:
 --   -----------
 --   ∅ ∣ xs = ∅
 -- R-Member:
 --   (x ∈ xs) (Γ ∣ xs = Γ1)
 --   ---------------------
 --   Γ,x:T ∣ xs = Γ1,x:T
 -- R-NotMember:
 --   (x ∉ xs) (Γ ∣ xs = Γ1)
 --   ----------------------
 --   Γ,x:T ∣ xs = Γ1
 -- InfRule [] "R-Empty" (rj envnil vxs envnil),
 -- InfRule [mj vx vxs,
 --          rj vC vxs vC1] "R-Member"
 --         (rj (envtm vC vx vT) vxs (envtm vC1 vx vT)),
 -- InfRule [nj vx vxs,
 --          rj vC vxs vC1] "R-NotMember"
 --         (rj (envtm vC vx vT) vxs vC1),

 -- MJ (membership judgment)
 -- M-Eq:
 --   --------
 --   x ∈ x xs
 -- M-Neq:
 --   (x≠y) (x ∈ xs)
 --   --------------
 --   x ∈ y xs
 -- InfRule [] "M-Eq" (mj vx (idcons vx vxs)),
 -- InfRule [Neq vx vy,
 --          mj vx vxs] "M-Neq"
 --         (mj vx (idcons vy vxs)),

 -- NJ (not membership judgment)
 -- N-Nil:
 --   ------
 --   x ∉ []
 -- N-Neq:
 --   (x≠y) (x ∉ xs)
 --   --------------
 --   x ∉ y xs
 -- InfRule [] "N-Nil" (nj vx idnil),
 -- InfRule [Neq vx vy,
 --          nj vx vxs] "N-Neq"
 --         (nj vx (idcons vy vxs)),

 -- IJ (import judgment)
 -- I-Nil:
 --   ------
 --   rep ⊢ [] ▹ ∅
 -- I-Import:
 --   (rep ⊢ imps ▹ Γ1) (mid:Γ0 ∈ rep) (Γ0 ⊕ Γ1 = Γ)
 --   --------------------------------------------
 --   rep ⊢ import mid imps ▹ Γ
 -- I-ImportOnly:
 --   (rep imps ▹ Γ1) (mid:Γ0 ∈ rep) (Γ0 ∣ xs = Γ0') (Γ0' ⊕ Γ1 = Γ)
 --   --------------------------------------------------------------
 --   rep ⊢ import mid only xs imps ▹ Γ
 InfRule [] "I-Nil" (ij vrep impnil envnil),
 InfRule [ij vrep vimps vC1,
          lj vmid vC0 vrep,
          uj vC0 vC1 vC
         ] "I-Import"
         (ij vrep (impcons (imp vmid) vimps) vC),
 -- InfRule [ij vimps vC1,
 --          lj vmid vC0 rep,
 --          rj vC0 vxs vC0',
 --          uj vC0' vC1 vC] "I-ImportOnly"
 --         (ij rep (impcons (imponly vmid vxs) vimps) vC),

 -- SJ (signature judgment)
 -- S-Module:
 --   (rep ⊢ imps ▹ Γ) (Γ ⊢ defs ⇒ Δ)
 --   ---------------------------
 --   rep ⊢ module mid imps defs : Δ
 InfRule [ij vrep vimps vC,
          dj vC vdfs vCD -- ,
          -- uj vC vCD vC1
         ] "S-Module"
         (sj vrep (md vmid vimps vdfs) vCD),

 -- DJ (definition judgment)
 -- D-Nil:
 --   ------------
 --   Γ ⊢ [] ⇒ ∅
 -- D-Val:
 --   (x∉dom(Γ)) (Γ ⊢ t : T) (Γ,x:T ⊢ defs ⇒ Γ1) (∅,x:T ⊕ Γ1 = Γ2)
 --   --------------------------------------------------------------
 --   Γ ⊢ val x = t defs ⇒ Γ2
 InfRule [] "D-Nil"
         (dj vC dfnil envnil),
 InfRule [fj vx vC,
          tj vC vt vT,
          dj (envtm vC vx vT) vdfs vC1,
          uj (envtm envnil vx vT) vC1 vC2] "D-Val"
         (dj vC (dfcons vx vt vdfs) vC2)
 -- InfRule [fj vx vC,
 --          tj vC vt vT] "D-End"
 --         (dj vC (dfcons vx vt dfnil) (envtm envnil vx vT))
 ]

infRulesST :: [InfRule]
infRulesST = infRulesFJ ++ infRulesTJ ++ infRulesMod

lid :: String -> Expr
lid name = ELex (Lex name "ID")

lmid :: String -> Expr
lmid name = ELex (Lex name "MID")

lnat :: String -> Expr
lnat value = ELex (Lex value "NAT")
