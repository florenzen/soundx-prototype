module Substitution where

import Data.Maybe
import qualified Data.List as L
import qualified Data.Set as S
import qualified Data.Map as M

import Syntax

type Sub = M.Map Var Expr

mapSub :: (Expr -> Expr) -> Sub -> Sub
mapSub = M.map

applySubDeriv :: Sub -> Deriv -> Deriv
applySubDeriv sub (Asm judg) = Asm (applySubJudg sub judg)
applySubDeriv sub (Deriv derivs name judg) =
    Deriv (applySubDerivs sub derivs) name (applySubJudg sub judg)
applySubDeriv sub (Fail judg) = Fail (applySubJudg sub judg)

applySubDerivs :: Sub -> [Deriv] -> [Deriv]
applySubDerivs sub = map (applySubDeriv sub)

applySubJudgs :: Sub -> [Judg] -> [Judg]
applySubJudgs sub = map (applySubJudg sub)

applySubJudg :: Sub -> Judg -> Judg
applySubJudg sub (Judg exprs name) =
    Judg (applySubExprs sub exprs) name
applySubJudg sub (Neq expr1 expr2) =
    Neq (applySubExpr sub expr1) (applySubExpr sub expr2)

applySubExprs :: Sub -> [Expr] -> [Expr]
applySubExprs sub = map (applySubExpr sub)

applySubExpr :: Sub -> Expr -> Expr
applySubExpr sub (EVar var) = fromMaybe (EVar var) (M.lookup var sub)
applySubExpr sub (ECon name exprs) =
    ECon name (map (applySubExpr sub) exprs)
applySubExpr sub (ELex lex) = ELex lex

singletonSub :: Var -> Expr -> Sub
singletonSub var expr = M.singleton var expr

emptySub :: Sub
emptySub = M.empty

domSub :: Sub -> S.Set Var
domSub = M.keysSet

ranSub :: Sub -> S.Set Expr
ranSub = S.fromList . M.elems

composeSub :: Sub -> Sub -> Sub
composeSub sub1 sub2 =
    let sub2' = M.map (applySubExpr sub1) sub2
        sub1' = M.filterWithKey (\var expr -> var `M.notMember` sub2) sub1
    in sub1' `unionSub` sub2'

unionSub :: Sub -> Sub -> Sub
unionSub sub1 sub2 =
    let vars = S.toList (domSub sub1 `S.intersection` domSub sub2)
    in if all (\var -> sub1 M.! var == sub2 M.! var) vars then
           sub1 `M.union` sub2
       else
           error "unionSub: rhs of duplicate vars differ"

restrictSub :: Sub -> S.Set Var -> Sub
restrictSub sub varSet =
    M.filterWithKey (\ var expr -> var `S.member` varSet) sub

showSub :: Sub -> String
showSub sub =
    L.unlines $
     map (\(var,expr) -> show var ++ " |-> " ++ show expr) (M.toList sub)

varsSub :: Sub -> S.Set Var
varsSub sub =
    M.foldrWithKey (\var expr varSet -> varSet `S.union` varsExpr expr)
         (domSub sub) sub

toListSub :: Sub -> [(Var,Expr)]
toListSub = M.toList

fromListSub :: [(Var,Expr)] -> Sub
fromListSub = M.fromList
