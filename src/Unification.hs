module Unification where

-- import Debug.Trace

import Control.Monad.Error
import qualified Data.Set as S

import Substitution
import Syntax

te :: MonadError e m => e -> m a
te msg = -- trace ("U: " ++ msg) $
         throwError msg

unifyJudgs :: S.Set Var -> [(Judg,Judg)] -> Either String Sub
unifyJudgs varSet [] = return emptySub
unifyJudgs varSet ((judg1,judg2):eqs) = do
    sub <- unifyJudg varSet judg1 judg2
    sub1 <- unifyJudgs varSet (map (applySubJudg sub $$) eqs)
    return (sub1 `composeSub` sub)

unifyJudg :: S.Set Var -> Judg -> Judg -> Either String Sub
unifyJudg varSet (Judg exprs1 name1) (Judg exprs2 name2) =
    if name1 == name2 && length exprs1 == length exprs2 then
        unifyExprs varSet (zip exprs1 exprs2)
    else
        let msg = "Could not unify judgments: " ++
                  show (Judg exprs1 name1) ++ " = " ++
                  show (Judg exprs2 name2)
        in te msg
unifyJudg varSet (Neq expr11 expr12) (Neq expr21 expr22) =
    unifyExprs varSet [(expr11,expr21),(expr12,expr22)]
unifyJudg varSet (Cat expr1 exprs1) (Cat expr2 exprs2) =
    unifyExprs varSet (zip (expr1:exprs1) (expr2:exprs2))
unifyJudg varSet judg1 judg2 =
    let msg = "Could not unify judgments: " ++
               show judg1 ++ " = " ++
               show judg2
    in te msg

unifyExpr :: S.Set Var -> Expr -> Expr -> Either String Sub
unifyExpr varSet expr1 expr2 = unifyExprs varSet [(expr1,expr2)]

unifyExprs :: S.Set Var -> [(Expr,Expr)] -> Either String Sub
unifyExprs varSet [] = return emptySub
unifyExprs varSet ((EVar var1, EVar var2) : eqs) =
    if var1 == var2 then
        unifyExprs varSet eqs
    else do
      sub <- if var1 `S.member` varSet then
                 return $ var1 `singletonSub` EVar var2
             else if var2 `S.member` varSet then
                      return $ var2 `singletonSub` EVar var1
                  else
                      let msg = "Could not unify variables: " ++
                                show var1 ++ " and " ++ show var2
                      in te msg
      let eqs1 = map (applySubExpr sub $$) eqs
      sub1 <- unifyExprs varSet eqs1
      return (sub1 `composeSub` sub)
unifyExprs varSet ((EVar var, expr) : eqs) =
    if var `S.member` varSet then
        if var `S.member` varsExpr expr then
            te $ "Occurs check failed: " ++ show (EVar var) ++
                           " = " ++ show expr
        else do
          let sub = var `singletonSub` expr
              eqs1 = map (applySubExpr sub $$) eqs
          sub1 <- unifyExprs varSet eqs1
          return (sub1 `composeSub` sub)
    else
        te $ "Could not unify " ++ show (EVar var) ++ " = " ++
                   show expr ++ " since lhs is not a unification variable"
unifyExprs varSet ((expr, EVar var) : eqs) =
    unifyExprs varSet ((EVar var, expr) : eqs)
unifyExprs varSet ((ECon name1 exprs1, ECon name2 exprs2) : eqs) =
    if length exprs1 == length exprs2 && name1 == name2 then
        unifyExprs varSet (zip exprs1 exprs2 ++ eqs)
    else
        te $ "Could not unify: " ++
                   show (ECon name1 exprs1) ++ " = " ++
                   show (ECon name2 exprs2)
unifyExprs varSet ((ELex lex1, ELex lex2) : eqs) =
    if lex1 == lex2 then
        unifyExprs varSet eqs
    else
        te $ "Could not unify: " ++
                   show (ELex lex1) ++ " = " ++
                   show (ELex lex2)
unifyExprs varSet ((expr1,expr2) : eqs) =
    te $ "Could not unify: " ++
                   show expr1 ++ " = " ++
                   show expr2

($$) :: (a -> b) -> (a,a) -> (b,b)
f $$ (a1,a2) = (f a1, f a2)
