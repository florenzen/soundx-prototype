module Freshening where

-- import Debug.Trace
import qualified Data.Set as S
import qualified Data.List as L

import Syntax
import Substitution

freshInfRule ::  S.Set Var -> InfRule -> (Sub,InfRule)
freshInfRule varSet infRule = freshInfRuleSub varSet emptySub infRule

freshInfRuleSub :: S.Set Var -> Sub -> InfRule -> (Sub,InfRule)
freshInfRuleSub varSet sub (InfRule judgs name judg) =
    let (sub1,judg1:judgs1) =
         freshJudgs varSet sub (judg:judgs)
    in (sub1, InfRule judgs1 name judg1)

freshJudg :: S.Set Var -> Sub -> Judg -> (Sub,Judg)
freshJudg varSet sub (Neq expr1 expr2) =
    let (sub1,[expr11,expr21]) = freshExprs varSet sub [expr1,expr2]
    in (sub1, Neq expr11 expr21)
freshJudg varSet sub (Judg exprs name) =
    let (sub1,exprs1) = freshExprs varSet sub exprs
    in (sub1, Judg exprs1 name)

freshJudgs :: S.Set Var -> Sub -> [Judg] -> (Sub,[Judg])
freshJudgs varSet sub judgs =
    L.mapAccumL (freshJudg varSet) sub judgs

freshExpr :: S.Set Var -> Sub -> Expr -> (Sub,Expr)
freshExpr varSet sub (EVar var) =
    if var `S.member` domSub sub then
        (sub, applySubExpr sub (EVar var))
    else
        let varSetSub = S.map getEVarVar (ranSub sub)
            var1 = pickFreshVar (varSet `S.union` varSetSub) var
        in ((var `singletonSub` (EVar var1)) `unionSub` sub, EVar var1)
freshExpr varSet sub (ECon name exprs) =
    let (sub1,exprs1) = freshExprs varSet sub exprs
    in (sub1, ECon name exprs1)
freshExpr varSet sub (ELex lex) = (sub, ELex lex)

freshExprs :: S.Set Var -> Sub -> [Expr] -> (Sub,[Expr])
freshExprs varSet sub exprs =
    L.mapAccumL (freshExpr varSet) sub exprs

freshUnivRR :: S.Set Var -> UnivRR -> (Sub,UnivRR)
freshUnivRR varSet (UnivRR expr1 expr2) =
    let (sub1,expr11) = freshExpr varSet emptySub expr1
        (sub2,expr21) = freshExpr varSet sub1 expr2
    in (sub2, UnivRR expr11 expr21)

freshGrdRR :: S.Set Var -> GrdRR -> (Sub,GrdRR)
freshGrdRR varSet (GrdRR judgs exprs11 expr1 exprs12 name expr2) =
    let (sub1,judgs1) = freshJudgs varSet emptySub judgs
        (sub2,exprs111) = freshExprs varSet sub1 exprs11
        (sub3,expr11) = freshExpr varSet sub2 expr1
        (sub4,exprs121) = freshExprs varSet sub3 exprs12
        (sub5,expr21) = freshExpr varSet sub4 expr2
    in (sub5,GrdRR judgs1 exprs111 expr11 exprs121 name expr21)

pickFreshVar :: S.Set Var -> Var -> Var
pickFreshVar varSet (Var name nameS) = pickFreshVarCount 0
    where
      pickFreshVarCount :: Integer -> Var
      pickFreshVarCount n =
          if (Var (name ++ show n) nameS `S.member` varSet) then
              pickFreshVarCount (n+1)
          else
              Var (name ++ show n) nameS

pickFreshLex :: S.Set Lex -> Lex -> Lex
pickFreshLex lexSet (Lex string nameS) = pickFreshLexCount 0
    where
      pickFreshLexCount :: Integer -> Lex
      pickFreshLexCount n =
          if (Lex (string ++ show n) nameS `S.member` lexSet) then
              pickFreshLexCount (n+1)
          else
              Lex (string ++ show n) nameS
