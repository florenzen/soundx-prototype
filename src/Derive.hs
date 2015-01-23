module Derive where


import qualified Data.List as L
import qualified Data.Set as S

import           Freshening
import           Substitution
import           Syntax
import           Unification


type Answer = (Store,Deriv)

derive :: [Deriv] -> [InfRule] -> Judg -> Either String Deriv
derive derivsAsm infRules judg =
    case buildDerivation derivsAsm infRules judg of
      Left derivs -> Left (show (concatMap collectMessages derivs))
      Right deriv -> Right deriv

buildDerivation :: [Deriv] -> [InfRule] -> Judg
                 -> Either [Deriv] Deriv
buildDerivation derivsAsm infRules judg =
    let ans = deriveAns S.empty derivsAsm infRules emptyStore judg
        res = filterAns ans
    in case res of
         Left ans1 -> let ans2 = map (subVariables (varsDerivs derivsAsm)) ans1
                      in Left (map snd ans2)
         Right an1 -> Right (snd (subVariables (varsDerivs derivsAsm) an1))
    where
      filterAns ans =
          let ansSuccess = dropWhile (isFailed . snd) ans
          in if null ansSuccess then Left ans else Right (head ansSuccess)

deriveAns :: S.Set Var -> [Deriv] -> [InfRule] -> Store -> Judg -> [Answer]
deriveAns varSet derivsAsm infRules st judg@(Neq expr1 expr2) =
    let (ok, st1) = propagate (varsDerivs derivsAsm) [CNeq expr1 expr2] st
        ansConstr = if ok then
                        [(st1, Deriv [] "Neq" judg)]
                    else
                        [(st1, Fail judg)]
        ansAsm = deriveByAsm derivsAsm st judg
    in  filterAns (ansConstr++ansAsm)
deriveAns varSet derivsAsm infRules st judg@(Judg exprs name) =
    let varSetAsm = varsDerivs derivsAsm
        prs = possibleRules varSet varSetAsm infRules judg st
        ansInfRule =
            [ (st3, Deriv derivs nameIR judg)
            | (judgsIR, nameIR, eqs) <- prs,
              let (ok, st1) = propagate varSetAsm eqs st,
              ok,
              let varSet1 = varSet `S.union` varsJudgs judgsIR,
              (st2, derivs) <-
                  concatMapAccumL (deriveAns varSet1 derivsAsm infRules) st1 judgsIR,
              -- Disabled, see "BUT" note at deriveAnsForPremises
              -- ((st2, ok1), derivs) <-
              --     deriveAnsForPremises varSet1 derivsAsm infRules st1 judgsIR,
              -- ok1, -- Only continue of the previous call produced something usable
              let st3 = removeConflictingNeqs st2
              -- If derivs contains Fail then we could produce a Fail node
              -- here including the messages from the failed subderivations and
              -- a message specific to the rule nameIR. The messages from
              -- the subderivations could also be discarded.
              -- See the test12 in TestResolution.hs
            ]
        ansInfRule1 = if null ansInfRule then
                          [(st, Fail judg)] -- Here we can produce a judgement specific
                                            -- error message
                      else
                          ansInfRule
        ansAsm = deriveByAsm derivsAsm st judg
    in filterAns (ansInfRule1++ansAsm)

-- Derives answers for the list of judgements, one after the other.
-- If one judgement can only be answered with failure derivations,
-- the remaining judgements are not derived anymore. The boolean
-- flag in the return value indicates if derivation has been aborted.
-- It is True for the results are valid, False otherwise.
-- Aborting is necessary since otherwise a judgement to be
-- derived after a failed one might lead to n infinite loop because
-- the answers of the non-derivable judgement do not provide
-- enough bindings for the metavariables.
-- The rules S-DefEnd and S-DefCons of STLC are an example of this.
-- BUT: this stops finding more than one error.
deriveAnsForPremises :: S.Set Var -> [Deriv] -> [InfRule] -> Store -> [Judg]
                     -> [((Store, Bool), [Deriv])]
deriveAnsForPremises varSet derivsAsm infRules st judgs =
    let lift ok = map (\(st, deriv) -> ((st, ok), deriv))
        derive (st, ok) judg =
            if ok then
                let ans = deriveAns varSet derivsAsm infRules st judg
                in if any (isFailed . snd) ans then
                       lift False ans
                   else
                       lift ok ans
            else
                []
    in concatMapAccumL derive (st, True) judgs

deriveByAsm :: [Deriv] -> Store -> Judg -> [Answer]
deriveByAsm derivsAsm st judg =
    let varSetAsm = varsDerivs derivsAsm
        pas = possibleAssumptions varSetAsm derivsAsm judg
    in [ (st1, derivAsm)
       | (derivAsm, eqs) <- pas,
         let (ok, st1) = propagate varSetAsm eqs st,
         ok
       ]

filterAns :: [Answer] -> [Answer]
filterAns ans =
    let ans1 = filter (not . isFailed . snd) ans
    in if null ans1 then ans else ans1

subVariables :: S.Set Var -> Answer -> Answer
subVariables varSetAsm (st,deriv) =
    let sub = solve varSetAsm st
    in (st, applySubDeriv sub deriv)

possibleAssumptions :: S.Set Var -> [Deriv] -> Judg -> [(Deriv,[Constr])]
possibleAssumptions varSet [] judg = []
possibleAssumptions varSet (derivAsm:derivsAsm) judg =
    let varsUnify = varsJudg judg `S.difference` varSet
    in case unifyJudg varsUnify (concl derivAsm) judg of
         Left msg -> possibleAssumptions varSet derivsAsm judg
         Right sub -> (derivAsm, subToEqs sub) :
                      possibleAssumptions varSet derivsAsm judg

possibleRules :: S.Set Var -> S.Set Var -> [InfRule] -> Judg -> [Constr]
              -> [([Judg],Name,[Constr])]
possibleRules varSet varSetAsm [] judg st = []
possibleRules varSet varSetAsm (infRule:infRules) judg st =
    let varSetSt = varsStore st
        varSetJudg = varsJudg judg
        varSetAvoid = varSetAsm `S.union` varSetSt `S.union` varSetJudg `S.union` varSet
        (subFresh, infRuleFresh) = freshInfRule varSetAvoid infRule
        varSetInfRule = S.map getEVarVar (ranSub subFresh)
        varSetUnify = (varSetInfRule `S.union` varSetJudg) `S.difference` varSetAsm
        InfRule judgsP name judgC = infRuleFresh
    in case unifyJudg varSetUnify judg judgC of
         Left msg -> possibleRules varSet varSetAsm infRules judg st
         Right sub -> (judgsP, name, subToEqs sub) :
                      possibleRules varSet varSetAsm infRules judg st

isFailed :: Deriv -> Bool
isFailed (Fail judg) = True
isFailed (Deriv derivs name judg) = any isFailed derivs
isFailed (Asm judg) = False

collectMessages :: Deriv -> [String]
collectMessages (Fail judg) = [show judg]
collectMessages (Deriv derivs name judg) =
    concatMap collectMessages derivs
collectMessages (Asm judg) = []

type Store = [Constr]

emptyStore :: [Constr]
emptyStore = []

data Constr = CEq Expr Expr
            | CNeq Expr Expr
instance Show Constr where
    show (CEq expr1 expr2) = show expr1 ++ " == " ++ show expr2
    show (CNeq expr1 expr2) = show expr1 ++ " |= " ++ show expr2

isCEq :: Constr -> Bool
isCEq (CEq _ _) = True
isCEq _ = False

propagate :: S.Set Var -> [Constr] -> Store -> (Bool, Store)
propagate varSet constrs st = simplify varSet (constrs++st)

removeConflictingNeqs :: Store -> Store
removeConflictingNeqs st =
    let (eqs, neqs) = L.partition isCEq st
        neqs1 = remove neqs
    in eqs++neqs1
    where
      remove [] = []
      remove (constr@(CNeq (EVar var1) expr2) : constrs) = constr : remove constrs
      remove (constr@(CNeq expr1 (EVar var2)) : constrs) = constr : remove constrs
      remove (constr@(CNeq expr1 expr2) : constrs) =
          if expr1 == expr2 then
              remove constrs
          else
              constr : remove constrs

simplify :: S.Set Var -> Store -> (Bool, Store)
simplify varSetAsm st =
    let (eqs, neqs) = L.partition isCEq st
        exprPairs = map (\(CEq expr1 expr2) -> (expr1,expr2)) eqs
        varSetEqs = varsStore eqs
        varSetUnify = varSetEqs `S.difference` varSetAsm
    in case unifyExprs varSetUnify exprPairs of
         Left msg -> (False, st)
         Right sub ->
             let neqs1 = map (applySubConstr sub) neqs
             in if satisfiable neqs1 then
                    (True, subToEqs sub ++ neqs1)
                else
                    (False, subToEqs sub ++ neqs1)

solve :: S.Set Var -> Store -> Sub
solve varSetAsm st =
    let (ok, st1) = simplify varSetAsm st
    in if ok then
           let (eqs,neqs) = L.partition isCEq st
               subEqs = fromListSub (map (\(CEq (EVar var) expr) -> (var,expr)) eqs)
               subNeqs = assign neqs
           in subNeqs `composeSub` subEqs
       else
           emptySub

applySubConstr :: Sub -> Constr -> Constr
applySubConstr sub (CEq expr1 expr2) =
    CEq (applySubExpr sub expr1) (applySubExpr sub expr2)
applySubConstr sub (CNeq expr1 expr2) =
    CNeq (applySubExpr sub expr1) (applySubExpr sub expr2)

assign :: [Constr] -> Sub
assign constrs =
    let lexSet = S.fromList $ concatMap extractLexs constrs
        vars = concatMap extractVars constrs
    in fst $ foldl assignVar (emptySub,lexSet) vars
    where
      extractLexs (CNeq (ELex lex1) (ELex lex2)) = [lex1,lex2]
      extractLexs (CNeq (ELex lex1) _) = [lex1]
      extractLexs (CNeq _ (ELex lex2)) = [lex2]
      extractLexs (CNeq _ _) = []
      extractVars (CNeq (EVar var1) (EVar var2)) = [var1,var2]
      extractVars (CNeq (EVar var1) _) = [var1]
      extractVars (CNeq _ (EVar var2)) = [var2]
      extractVars (CNeq _ _) = []
      assignVar (sub,lexSet) var@(Var name nameS) =
          let lex1 = pickFreshLex lexSet (Lex name nameS)
          in (sub `composeSub` singletonSub var (ELex lex1), S.insert lex1 lexSet)

satisfiable :: [Constr] -> Bool
satisfiable [] = True
satisfiable (CNeq (EVar var1) expr2 : constrs) = satisfiable constrs
satisfiable (CNeq expr1 (EVar var2) : constrs) = satisfiable constrs
satisfiable (CNeq expr1 expr2 : constrs) =
    if expr1 == expr2 then
        False
    else
        satisfiable constrs

subToEqs :: Sub -> [Constr]
subToEqs sub = map (\(var,expr) -> EVar var `CEq` expr) (toListSub sub)

varsStore :: Store -> S.Set Var
varsStore st = S.unions (map varsConstr st)

varsConstr :: Constr -> S.Set Var
varsConstr (CNeq expr1 expr2) = varsExpr expr1 `S.union` varsExpr expr2
varsConstr (CEq expr1 expr2) = varsExpr expr1 `S.union` varsExpr expr2


concatMapAccumL :: (acc -> x -> [(acc, y)]) -> acc -> [x] -> [(acc, [y])]
concatMapAccumL f acc [] = [(acc,[])]
concatMapAccumL f acc (x:xs) =
    [ (acc2, x1:xs2)
    | (acc1, x1) <- f acc x,
      (acc2, xs2) <- concatMapAccumL f acc1 xs
    ]
