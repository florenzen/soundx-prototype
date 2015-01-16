module Matching where

import Debug.Trace

import Test.HUnit
import qualified Data.List as L
import qualified Data.Set as S

import Syntax
import Substitution


matchExpr :: Expr -> Expr -> Maybe Sub
matchExpr (EVar var) expr = return $ var `singletonSub` expr
matchExpr (ECon name1 exprList1) (ECon name2 exprList2) =
    if name1 == name2 && length exprList1 == length exprList2 then
        matchExprList (zip exprList1 exprList2)
    else
        Nothing
matchExpr expr1 expr2 = Nothing



matchPatJudg :: Pat -> Judg -> Maybe (Sub,CtxJ)
matchPatJudg (PatJ exprList11 expr1 exprList12 name1) (Judg exprList2 name2) = do
    let len1 = length exprList11 + 1 + length exprList12
    if name1 == name2 && len1 == length exprList2 then do
        let (exprList21,expr2:exprList22) =
                L.splitAt (length exprList11) exprList2
        sub1 <- matchExprList (zip (exprList11++exprList12)
                               (exprList21++exprList22))
        sub2 <- matchExpr expr1 expr2
        return (sub1 `unionSub` sub2, CtxJ exprList21 CEHole exprList22 name2)
    else
        Nothing
matchPatJudg (PatE expr1) (Judg exprList2 name) = do
    (sub,exprList1,ctxE,exprList2) <- matchExprListTD expr1 exprList2
    return (sub, CtxJ exprList1 ctxE exprList2 name)

matchExpr :: Expr -> Expr -> Maybe Sub
matchExpr (EVar var) expr = return $ var `singletonSub` expr
matchExpr (ECon name1 exprList1) (ECon name2 exprList2) =
    if name1 == name2 && length exprList1 == length exprList2 then
        matchExprList (zip exprList1 exprList2)
    else
        Nothing
matchExpr expr1 expr2 = Nothing

matchExprList :: [(Expr,Expr)] -> Maybe Sub
matchExprList [] = return emptySub
matchExprList ((expr1,expr2):exprList) = do
  sub1 <- matchExpr expr1 expr2
  sub2 <- matchExprList exprList
  return $ sub1 `unionSub` sub2

matchExprTD :: Expr -> Expr -> Maybe (Sub,CtxE)
matchExprTD expr1 (ECon name2 exprList2) =
    case matchExpr expr1 (ECon name2 exprList2) of
      Just sub -> return (sub,CEHole)
      Nothing -> do
          (sub,exprList21,ctxE,exprList22) <- matchExprListTD expr1 exprList2
          return (sub, CECon name2 exprList21 ctxE exprList22)
matchExprTD expr1 (EVar var) = Nothing

matchExprListTD :: Expr -> [Expr] -> Maybe (Sub,[Expr],CtxE,[Expr])
matchExprListTD expr1 [] = Nothing
matchExprListTD expr1 (expr2:exprList2)=
    case matchExprTD expr1 expr2 of
      Just (sub,ctxE) -> return (sub,[],ctxE,exprList2)
      Nothing -> do
        (sub,exprList21,ctxE,exprList22) <- matchExprListTD expr1 exprList2
        return (sub,expr2:exprList21,ctxE,exprList22)

applyCtxJ :: CtxJ -> Expr -> Judg
applyCtxJ (CtxJ exprList1 ctxE exprList2 name) expr =
    Judg (exprList1 ++ [applyCtxE ctxE expr] ++ exprList2) name

applyCtxE :: CtxE -> Expr -> Expr
applyCtxE CEHole expr = expr
applyCtxE (CECon name exprList1 ctxE exprList2) expr =
    ECon name (exprList1 ++ [applyCtxE ctxE expr] ++ exprList2)

consistent :: Sub -> Sub -> Bool
consistent sub1 sub2 =
    let varList = S.toList (domSub sub1 `S.intersection` domSub sub2)
    in all check varList
    where
      check var = applySubExpr sub1 (EVar var) == applySubExpr sub2 (EVar var)

consistentList :: [Sub] -> Bool
consistentList subList =
    all (uncurry consistent) [ (sub1,sub2) | sub1 <- subList, sub2 <- subList ]


-- Test cases

patJ01 = PatJ [EVar (Var "C")]
         (ECon "pair" [EVar (Var "t1"), EVar (Var "t2")])
         [EVar (Var "T")] "TJ"

patE01 = PatE
          (ECon "let" [EVar (Var "x "), EVar (Var "T1"), EVar (Var "t1"),
                       EVar (Var "t2")])
patE02 = PatE (EVar (Var "x"))
patE03 = PatE (ECon "a" [EVar (Var "X"), EVar (Var "Y")])
patE04 = PatE (ECon "c" [ECon "d" []])
patE05 = PatE (ECon "c" [EVar (Var "X")])

judg01 = Judg [ECon "envnil" [],
               ECon "pair" [ECon "num1" [], ECon "num2" []],
                    ECon "Pair" [EVar (Var "T1"), EVar (Var "T2")]] "TJ"
judg02 = Judg [ECon "envnil" [],
               ECon "add" [(ECon "num1" []),
                           (ECon "let" [ECon "a" [], ECon "num2" [],
                                        ECon "Nat" [],
                                        ECon "var" [ECon "a" []]])],
               ECon "Nat" []] "TJ"
judg03 = Judg [ECon "envnil" [],
               ECon "a" [ECon "b" [], ECon "c" [ECon "d" []]],
               ECon "Foo" []] "TJ"
judg04 = Judg [ECon "envnil" [],
               ECon "a" [ECon "b" [], ECon "e" [ECon "d" []],
                         ECon "c" [ECon "e" []]],
               ECon "Bar" []] "TJ"

test01 = (patJ01,judg01)
test02 = (patE01,judg02)
test03 = (patE03,judg03)
test04 = (patE04,judg03)
test05 = (patE05,judg04)
test06 = (patE05,judg03)

testCases = [test01,test02,test03,test04,test05,test06]

testSuite = TestList
            (map (TestCase . makeTestCaseMatch) testCases)

makeTestCaseMatch (pat@(PatE expr), judg) =
    case matchPatJudg pat judg of
      Nothing -> assertFailure (show pat ++ " expected to match " ++ show judg)
      Just (sub,ctxJ) ->
          assertBool ("Context and substitution dont't recover judgment")
                         (applyCtxJ ctxJ (applySubExpr sub expr) == judg)

makeTestCaseMatch (pat@(PatJ exprList1 expr exprList2 name), judg) =
    case matchPatJudg pat judg of
      Nothing -> assertFailure (show pat ++ " expected to match " ++ show judg)
      Just (sub,ctxJ) ->
          assertBool ("Context and substitution dont't recover judgment")
                         (applyCtxJ ctxJ (applySubExpr sub expr) == judg)
