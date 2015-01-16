module Variables where

import Syntax

-- evar :: Name -> Expr
-- evar name = ECon name []
-- evA :: Expr
-- evA = evar "a"
-- evB :: Expr
-- evB = evar "b"
-- evC :: Expr
-- evC = evar "c"
-- evD :: Expr
-- evD = evar "d"
-- evE :: Expr
-- evE = evar "e"
-- evF :: Expr
-- evF = evar "f"
-- evG :: Expr
-- evG = evar "g"
-- evA1 :: Expr
-- evA1 = evar "a1"
-- evB1 :: Expr
-- evB1 = evar "b1"
-- evC1 :: Expr
-- evC1 = evar "c1"
-- evD1 :: Expr
-- evD1 = evar "d1"
-- evE1 :: Expr
-- evE1 = evar "e1"
-- evF1 :: Expr
-- evF1 = evar "f1"
-- evG1 :: Expr
-- evG1 = evar "g1"
-- evA2 :: Expr
-- evA2 = evar "a2"
-- evB2 :: Expr
-- evB2 = evar "b2"
-- evC2 :: Expr
-- evC2 = evar "c2"
-- evD2 :: Expr
-- evD2 = evar "d2"
-- evE2 :: Expr
-- evE2 = evar "e2"
-- evF2 :: Expr
-- evF2 = evar "f2"
-- evG2 :: Expr
-- evG2 = evar "g2"

-- modid :: Name -> Expr
-- modid name = ECon name []
-- modA :: Expr
-- modA = modid "MA"
-- modB :: Expr
-- modB = modid "MB"
-- modC :: Expr
-- modC = modid "MC"
-- modD :: Expr
-- modD = modid "MD"
-- modE :: Expr
-- modE = modid "ME"
-- modF :: Expr
-- modF = modid "MF"
-- modG :: Expr
-- modG = modid "MG"

mvar :: Name -> Name -> Expr
mvar name nameS = EVar (Var name nameS)
vC :: Expr
vC = mvar "C" "Env"
vC0 :: Expr
vC0 = mvar "C0" "Env"
vC0' :: Expr
vC0' = mvar "C0'" "Env"
vC1 :: Expr
vC1 = mvar "C1" "Env"
vC2 :: Expr
vC2 = mvar "C2" "Env"
vCD :: Expr
vCD = mvar "CD" "Env"
vx :: Expr
vx = mvar "x" "ID"
vy :: Expr
vy = mvar "y" "ID"
vz :: Expr
vz = mvar "z" "ID"
vx1 :: Expr
vx1 = mvar "x1" "ID"
vy1 :: Expr
vy1 = mvar "y1" "ID"
vz1 :: Expr
vz1 = mvar "z1" "ID"
vx2 :: Expr
vx2 = mvar "x2" "ID"
vy2 :: Expr
vy2 = mvar "y2" "ID"
vz2 :: Expr
vz2 = mvar "z2" "ID"
vn :: Expr
vn = mvar "n" "NAT"
vxs :: Expr
vxs = mvar "xs" "Ids"
vT :: Expr
vT = mvar "T" "Type"
vT1 :: Expr
vT1 = mvar "T1" "Type"
vT2 :: Expr
vT2 = mvar "T2" "Type"
vT11 :: Expr
vT11 = mvar "T11" "Type"
vT12 :: Expr
vT12 = mvar "T12" "Type"
vS :: Expr
vS = mvar "S" "Type"
vS1 :: Expr
vS1 = mvar "S1" "Type"
vS2 :: Expr
vS2 = mvar "S2" "Type"
vU :: Expr
vU = mvar "U" "Type"
vU1 :: Expr
vU1 = mvar "U1" "Type"
vU2 :: Expr
vU2 = mvar "U2" "Type"
vt :: Expr
vt = mvar "t" "Term"
vt1 :: Expr
vt1 = mvar "t1" "Term"
vt2 :: Expr
vt2 = mvar "t2" "Term"
vt3 :: Expr
vt3 = mvar "t3" "Term"
vt4 :: Expr
vt4 = mvar "t4" "Term"
vs :: Expr
vs = mvar "s" "Term"
vs1 :: Expr
vs1 = mvar "s1" "Term"
vs2 :: Expr
vs2 = mvar "s2" "Term"
vBs :: Expr
vBs = mvar "bdgs" "Bindings"
vBNNs :: Expr
vBNNs = mvar "bdgs" "BindingsNN"
vBBLs :: Expr
vBBLs = mvar "bdgs" "BindingsBL"
vmid :: Expr
vmid = mvar "mid" "MID"
vmid1 :: Expr
vmid1 = mvar "mid1" "MID"
vrep :: Expr
vrep = mvar "rep" "Rep"
vdfs :: Expr
vdfs = mvar "dfs" "Defs"
vimps :: Expr
vimps = mvar "imps" "Imports"

-- neq :: Expr -> Expr -> Judg
-- neq x y = Judg [x,y] "neq"
-- neqMId :: Expr -> Expr -> Judg
-- neqMId mid1 mid2 = Judg [mid1,mid2] "neqMId"

-- fvnil :: Expr
-- fvnil = ECon "fvnil" []
-- fvcons :: Expr -> Expr -> Expr
-- fvcons x xs = ECon "fvcons" [x,xs]

-- evars :: [Expr]
-- evars = [evA,evB,evC,evD,evE,evF,evG] ++
--         [evA1,evB1,evC1,evD1,evE1,evF1,evG1] ++
--         [evA2,evB2,evC2,evD2,evE2,evF2,evG2]

-- mids :: [Expr]
-- mids = [modA,modB,modC,modD,modE,modF,modG]

-- fvs :: Expr
-- fvs = foldr fvcons fvnil evars

-- infRulesNeq :: [InfRule]
-- infRulesNeq =
--   [ InfRule [] ("neq" ++ show x ++ show y) (neq x y)
--         | x <- evars, y <- evars, x /= y ]

-- infRulesNeqMId :: [InfRule]
-- infRulesNeqMId =
--   [ InfRule [] ("neqMid" ++ show mid1 ++ show mid2) (neqMId mid1 mid2)
--             | mid1 <- mids, mid2 <- mids, mid1 /= mid2 ]

-- aritiesId :: [Arity]
-- aritiesId = [ Arity name [] "Id" | (ECon name []) <- evars ]

-- aritiesMId :: [Arity]
-- aritiesMId = [Arity name [] "MId" | (ECon name []) <- mids ]
