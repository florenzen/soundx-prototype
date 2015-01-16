module WFBase where

import Control.Monad
import Control.Monad.Error
import Data.Either.Utils
import Data.Maybe

import Syntax
import Utils

wfSortDecls :: [SortDecl] -> Either String ()
wfSortDecls [] = return ()
wfSortDecls (SortDecl name stype : sdecls) = do
  when (name `elem` map getSortDeclName sdecls)
         (throwError $ "Duplicate sort name " ++ name)
  wfSortDecls sdecls

wfArities :: [SortDecl] -> [Arity] -> Either String ()
wfArities sdecls [] = return ()
wfArities sdecls (Arity name names0 name0 : arities) = do
  when (name `elem` map getArityName arities)
           (throwError "Duplicate constructor name")
  stype0:stypes0 <-
      mapM (\name ->
            maybeToEither ("unknown sort in arity declaration " ++ name)
            (findSortDecl sdecls name)) (name0:names0)
  when (getSortDeclType stype0 == Lexical)
         (throwError $ "result sort of constructor cannot be lexical for " ++ name)
  wfArities sdecls arities

wfForms :: [SortDecl] -> [Form] -> Either String ()
wfForms sdecls [] = return ()
wfForms sdecls (Form name names0 : forms) = do
  when (name `elem` map getFormName forms)
           (throwError "Duplicate judgment name")
  mapM_ (\name ->
             maybeToEither ("unknown sort in form declaration " ++ name)
             (findSortDecl sdecls name)) names0
  wfForms sdecls forms

wfExpr :: [SortDecl] -> [Arity] -> Expr -> Either String Name
wfExpr sdecls arities (EVar (Var name nameS)) = do
    sdecl <- maybeToEither ("unknown sort " ++ nameS ++ " in variable " ++ name)
             (findSortDecl sdecls nameS)
    return nameS
wfExpr sdecls arities (ELex (Lex string nameS)) = do
    sdecl <- maybeToEither ("unknown sort " ++ nameS ++ " in lexical constant " ++ string)
             (findSortDecl sdecls nameS)
    when (getSortDeclType sdecl /= Lexical)
         (throwError $ "lexical constant " ++ string ++ " not of lexical type (sort " ++ nameS ++ ")")
    return nameS
wfExpr sdecls arities (ECon name exprs) = do
  Arity _ names name0 <- maybeToEither ("arity not found: " ++ name)
                         (findArity arities name)
  namesS <- mapM (wfExpr sdecls arities) exprs
  unless (namesS == names)
             (throwError $ "constructor applied to wrong arguments: " ++ name ++
             "\narity: " ++ show (Arity name names name) ++
             "\narguments: " ++ show namesS)
  return name0

wfJudg :: [SortDecl] -> [Arity] -> [Form] -> Judg -> Either String ()
wfJudg sdecls arities forms (Neq expr1 expr2) = do
  nameS1 <- wfExpr sdecls arities expr1
  nameS2 <- wfExpr sdecls arities expr2
  when (nameS1 /= nameS2)
             (throwError $ "sorts of Neq arguments must be the same: " ++
              show expr1 ++ " /= " ++ show expr2)
  let stype1 = getSortDeclType $ fromJust $ findSortDecl sdecls nameS1
      stype2 = getSortDeclType $ fromJust $ findSortDecl sdecls nameS2
  when (stype1 /= Lexical || stype2 /= Lexical)
             (throwError $ "Neq only allowed for lexical sorts: " ++
              show expr1 ++ " /= " ++ show expr2)
wfJudg sdecls arities forms (Cat expr exprs) = do
  nameS <- wfExpr sdecls arities expr
  namesS <- mapM (wfExpr sdecls arities) exprs
  unless (foldr (\name r -> r && name == nameS) True namesS)
             (throwError $ "all arguments to Cat must be of the same sort")
  let stypes = map (getSortDeclType . fromJust . findSortDecl sdecls) (nameS:namesS)
  when (any (/= Lexical) stypes)
           (throwError $ "Cat only allowed for lexical sorts")
wfJudg sdecls arities forms (Judg exprs name) = do
  Form _ names <- maybeToEither ("form not found: " ++ name)
                  (findForm forms name)
  namesS <- mapM (wfExpr sdecls arities) exprs
  unless (namesS == names)
             (throwError $ "judgment applied to wrong arguments: " ++ name +%+
             show exprs)

wfInfRules :: [SortDecl] -> [Arity] -> [Form] -> [InfRule] -> Either String ()
wfInfRules sdecls arities forms [] = return ()
wfInfRules sdecls arities forms (InfRule judgs name judg : infRules) = do
  when (name `elem` map getInfRuleName infRules)
           (throwError "Duplicate rule name")
  mapM_ (wfJudg sdecls arities forms) (judg:judgs)
  wfInfRules sdecls arities forms infRules

wfImpCons :: [Arity] -> Name -> Name -> [Name] -> Either String ()
wfImpCons arities modIdSort impSort [] = return ()
wfImpCons arities modIdSort impSort (name:names) = do
  Arity _ names1 name0 <- maybeToEither ("arity not found: " ++ name)
                          (findArity arities name)
  unless (name0 == impSort)
             (throwError "import constructor with wrong range")
  unless (if length names1 > 0 then names1!!0 == modIdSort else False)
             (throwError ("import constructor with wrong domain: " ++ name))
  wfImpCons arities modIdSort impSort names

wfBase :: Base -> Either String ()
wfBase base = do
  let sdecls = getBaseSortDecls base
      arities = getBaseArities base
      forms = getBaseForms base
      infRules = getBaseInfRules base

  -- Module system definition
  let modIdSort = getBaseModIdSort base
      impsSort = getBaseImpsSort base
      impSort = getBaseImpSort base
      modSort = getBaseModSort base
      modCon = getBaseModCon base
      impsConNil = getBaseImpsConNil base
      impsConCons = getBaseImpsConCons base
      impCons = getBaseImpCons base
      sigSort = getBaseSigSort base
      sigJudg = getBaseSigJudg base
      sigRepSort = getBaseSigRepSort base
      sigRepCons = getBaseSigRepConCons base
      sigRepNil = getBaseSigRepConNil base

  -- Basics
  -- Constructor arities and judgment forms
  wfArities sdecls arities
  wfForms sdecls forms

  -- Type system
  wfInfRules sdecls arities forms infRules

  -- Module system
  -- Declaration of import constructors
  wfImpCons arities modIdSort impSort impCons

  -- Declaration of import list constructors
  Arity _ names name0 <- maybeToEither ("arity not found: " ++ show impsConNil)
                         (findArity arities impsConNil)
  unless (names == [] && name0 == impsSort)
             (throwError "import list nil with wrong arity")
  Arity _ names name0 <- maybeToEither ("arity not found: " ++ show impsConCons)
                         (findArity arities impsConCons)

  unless (names == [impSort,impsSort] && name0 == impsSort)
             (throwError "import list cons with wrong arity")

  -- Arity of module constructor
  Arity _ names name0 <- maybeToEither ("arity not found: " ++ show modCon)
                         (findArity arities modCon)

  unless (if length names > 1 then
              names!!0 == modIdSort &&
              names!!1 == impsSort
          else
              False)
             (throwError "module constructor with wrong arity")
  unless (name0 == modSort)
             (throwError "module constructor with wrong range")

  -- Signature judgment form
  Form _ names <- maybeToEither ("form not found: " ++ sigJudg)
                  (findForm forms sigJudg)
  unless (names == [sigRepSort,modSort,sigSort])
             (throwError "wrong form for signature judgment")

  -- Repository list constructors
  Arity _ names name0 <- maybeToEither ("arity not found: " ++ show sigRepNil)
                         (findArity arities sigRepNil)
  unless (name0:names == [sigRepSort])
             (throwError $ "wrong arity for " ++ sigRepNil)
  Arity _ names name0 <- maybeToEither ("arity not found: " ++ show sigRepCons)
                         (findArity arities sigRepCons)
  unless (name0:names == [sigRepSort,modIdSort,sigSort,sigRepSort])
             (throwError $ "wrong arity for " ++ sigRepCons +%+
                         show (name0:names))
