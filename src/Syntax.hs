module Syntax where

import Prelude hiding (showList)
import qualified Data.List as L
import qualified Data.Set as S
import System.Cmd

import Utils

type Name = String

data SortType = Lexical | ContextFree
                deriving Eq
data SortDecl = SortDecl {getSortDeclName::Name,
                          getSortDeclType::SortType}
              deriving Eq
data Arity = Arity {getArityName::Name,
                    getArityArgs::[Name],
                    getArityRes::Name}
           deriving Eq
data Form = Form {getFormName::Name,
                  getFormArgs::[Name]}
          deriving Eq
data Var = Var {getVarName::Name,
                getVarSort::Name}
data Lex = Lex {getLexValue::String,
                getLexSort::Name}
         deriving (Ord,Eq)
instance Ord Var where
    (Var name1 _) <= (Var name2 _) = name1 <= name2
instance Eq Var where
    (Var name1 _) == (Var name2 _) = name1 == name2

data Expr = EVar {getEVarVar::Var}
          | ELex {getELexLex::Lex}
          | ECon {getEConName::Name,
                  getEConExprs::[Expr]}
          deriving (Ord,Eq)
data Judg = Judg {getJudgExpr::[Expr],
                  getJudgName::Name}
          | Neq {getNeqLhs::Expr,
                 getNeRhs::Expr}
          | Cat {getCatLhs::Expr,
                 getCatRhs::[Expr]}
          deriving Eq
data InfRule = InfRule {getInfRuleJudgsP::[Judg],
                        getInfRuleName::Name,
                        getInfRuleJudgC::Judg}
             deriving Eq
data UnivRR = UnivRR {getUnivRRLhs::Expr,
                      getUnivRRRhs::Expr}
            deriving Eq
data GrdRR = GrdRR {getGrdRRJudgsP::[Judg],
                    getGrdRRExprs1::[Expr],
                    getGrdRRExpr::Expr,
                    getGrdRRExprs2::[Expr],
                    getGrdRRName::Name,
                    getGrdRRRhs::Expr}
           deriving Eq
data Deriv = Deriv {getDerivSubs::[Deriv],
                    getDerivName::Name,
                    getDerivConcl::Judg}
           | Asm {getAsmConcl::Judg}
           | Fail {getFailJudg::Judg}
           deriving Eq
data Base = Base {getBaseSortDecls::[SortDecl],
                  getBaseArities::[Arity],
                  getBaseForms::[Form],
                  getBaseInfRules::[InfRule],

                  -- Sorts
                  getBaseSigSort::Name,
                  getBaseModIdSort::Name,
                  getBaseImpsSort::Name,
                  getBaseImpSort::Name,
                  getBaseModSort::Name,
                  getBaseSigRepSort::Name,

                  -- Constructors
                  getBaseModCon::Name,
                  getBaseImpsConNil::Name,
                  getBaseImpsConCons::Name,
                  getBaseImpCons::[Name],
                  getBaseSigRepConNil::Name,
                  getBaseSigRepConCons::Name,

                  -- Signature judgment
                  getBaseSigJudg::Name}
data Ext = Ext {getExtSortDecls::[SortDecl],
                getExtArities::[Arity],
                getExtInfRules::[InfRule],
                getExtUnivRRs::[UnivRR],
                getExtGrdRRs::[GrdRR]}
         deriving Eq
data Mod = Mod {getModExpr::Expr,
                getModExt::Ext}
data Intf = Intf {getIntfId::Expr,
                  getIntfExpr::Expr,
                  getIntfExts::[Ext]}
data InfRuleClass = PB | PE deriving (Show, Eq)

concl :: Deriv -> Judg
concl (Deriv derivs name judg) = judg
concl (Asm judg) = judg
concl (Fail judg) = judg

instance Show SortType where
    show Lexical = "LEX"
    show ContextFree = "CF"
instance Show SortDecl where
    show (SortDecl name stype) = name ++ ":" ++ show stype
instance Show Var where
    show (Var name nameS) = name -- ++ ":" ++ nameS
instance Show Lex where
    show (Lex str nameS) = str
instance Show Expr where
    show (EVar var) = show var
    show (ECon name exprs) =
        name ++ "(" ++ showList "," exprs ++ ")"
    show (ELex lex) = show lex
instance Show Judg where
    show (Judg exprs name) =
        "(" ++ showList "," exprs ++ ")" ++
                " " ++ name
    show (Neq expr1 expr2) =
        show expr1 ++ " |= " ++ show expr2
instance Show InfRule where
    show (InfRule judgs name judg) =
        showList " ∧ " judgs ++
               " =" ++ name ++ "=> " ++ show judg
instance Show UnivRR where
    show (UnivRR expr expr') =
        show expr ++ "~~~>" ++ show expr'
instance Show GrdRR where
    show (GrdRR judgs exprs1 expr exprs2 name expr') =
        "(" ++ showList " ∧ " judgs ++ " ==> " ++
                "(" ++ showList "," exprs1 ++
                ",[" ++ show expr ++ "]," ++
                showList "," exprs2 ++
                ") " ++ name ++ ") ~~~> " ++ show expr'
instance Show Arity where
    show (Arity name names name0) =
        name ++ ": " ++ show names ++ " -> " ++ name0
instance Show Ext where
    show (Ext sdecls arities infRules univRRs grdRRs) =
        "Sort declaration:" +%+
        showList "\n  " sdecls +%+
        "Arities:" +%+
        showList "\n  " arities +%+
        "Inference rules:" +%+
        showList "\n  " infRules +%+
        "Restricted desugaring:" +%+
        showList "\n  " grdRRs +%+
        "Universal desugarings:" +%+
        showList "\n  " univRRs
instance Show Intf where
    show (Intf exprId exprSig exts) =
        show exprId ++ ": " +%+
        show exprSig +%+
        show exts
instance Show Deriv where
    show (Asm judg) = "<> => " ++ show judg
    show (Deriv judgs name judg) =
        show judgs ++ "=" ++ name ++ "=>" ++ show judg
    show (Fail judg) = "!!! Could not derive " ++ show judg ++ " !!!"

-- |The empty extension
extEmpty :: Ext
extEmpty = Ext [] [] [] [] []


showList :: Show a => String -> [a] -> String
showList str list = concat (L.intersperse str (map show list))

-- |Merge the arities an inference rules of an extension
-- to a base system
mergeBX :: Base -> Ext -> Base
mergeBX base ext =
    base{getBaseSortDecls=getBaseSortDecls base ++ getExtSortDecls ext,
         getBaseArities=getBaseArities base ++ getExtArities ext,
         getBaseInfRules=getBaseInfRules base ++ getExtInfRules ext}

-- |Return all variables of an expression
varsExpr :: Expr -> S.Set Var
varsExpr (EVar var) = S.singleton var
varsExpr (ECon name exprs) = varsExprs exprs
varsExpr (ELex lex) = S.empty

-- |Return all variables of a list of expressions
varsExprs :: [Expr] -> S.Set Var
varsExprs exprs =
    foldr (\expr varSet -> varsExpr expr `S.union` varSet)
          S.empty exprs

-- |Return all variables of a judgment
varsJudg :: Judg -> S.Set Var
varsJudg (Judg exprs name) = varsExprs exprs
varsJudg (Neq expr1 expr2) = varsExpr expr1 `S.union` varsExpr expr2

-- |Return all variables of a list of judgment
varsJudgs :: [Judg] -> S.Set Var
varsJudgs judgs =
    foldr (\judg varSet -> varsJudg judg `S.union` varSet)
          S.empty judgs

-- |Return all variables of an inference rule
varsInfRule :: InfRule -> S.Set Var
varsInfRule (InfRule judgs name judg) =
    varsJudg judg `S.union` varsJudgs judgs

varsDeriv :: Deriv -> S.Set Var
varsDeriv (Deriv derivs name judg) =
    varsDerivs derivs `S.union` varsJudg judg
varsDeriv (Asm judg) = varsJudg judg
varsDeriv (Fail _) = S.empty

varsDerivs :: [Deriv] -> S.Set Var
varsDerivs derivs =
    foldr (\deriv varSet -> varsDeriv deriv `S.union` varSet)
          S.empty derivs

findSortDecl :: [SortDecl] -> Name -> Maybe SortDecl
findSortDecl [] name = Nothing
findSortDecl (SortDecl name1 stype : sdecls) name =
    if name1 == name then
        Just $ SortDecl name1 stype
    else
        findSortDecl sdecls name

findInfRule :: [InfRule] -> Name -> Maybe InfRule
findInfRule [] name = Nothing
findInfRule (InfRule judgs name1 judg : infRules) name =
    if name1 == name then
        Just $ InfRule judgs name1 judg
    else
        findInfRule infRules name

findArity :: [Arity] -> Name -> Maybe Arity
findArity [] name = Nothing
findArity (Arity name0 names name1 : arities) name =
    if name0 == name then
        Just $ Arity name0 names name1
    else
        findArity arities name

findForm :: [Form] -> Name -> Maybe Form
findForm [] name = Nothing
findForm (Form name0 names : forms) name =
    if name0 == name then
        Just $ Form name0 names
    else
        findForm forms name

-- |Translate derivation into a TeX document.
derivationsToTeXDoc :: [Deriv] -> String
derivationsToTeXDoc derivs =
    header ++
    (concat $ L.intersperse "\\bigskip" (map derivationToTeX derivs)) ++
    footer

-- |Translate a derivation to calls of the \\inference TeX macro.
derivationToTeX :: Deriv -> String
derivationToTeX (Asm judg) =
  show judg
derivationToTeX (Deriv derivs name judg) =
  "\\inference[" ++ name ++ "]" ++
  "{" ++ concat (L.intersperse "&" (map derivationToTeX derivs)) ++ "}" ++
  "{" ++ show judg ++ "}"

-- |Header of TeX file.
header :: String
header = "\\documentclass[landscape,fleqn]{article}" ++
         "\\usepackage[inference]{semantic}" ++
         "\\usepackage[papersize={500cm,500cm}]{geometry}" ++
         "\\usepackage{unicode-math}" ++
         "\\begin{document}"

-- |Footer of TeX file.
footer :: String
footer = "\\end{document}"

-- |Write a derivation to a TeX file and call lualatex on that file.
teXDerivations :: String -> [Deriv] -> IO ()
teXDerivations file derivs = do
  writeFile (file ++ ".tex") (derivationsToTeXDoc derivs)
  system ("lualatex " ++ file)
  return ()
