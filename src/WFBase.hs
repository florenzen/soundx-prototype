module WFBase where

import Control.Monad
import Control.Monad.Error
import Data.Either.Utils

import Syntax
import Utils


wfArities :: [Arity] -> [Arity] -> Either String ()
wfArities arities1 [] = return ()
wfArities arities1 (Arity name names0 name0 : arities) = do
  unless (not (name `elem` map getArityName arities1))
             (throwError "Duplicate constructor name")
  wfArities (arities1 ++ [Arity name names0 name0]) arities

wfForms :: [Form] -> [Form] -> Either String ()
wfForms forms1 [] = return ()
wfForms forms1 (Form name names0 : forms) = do
  unless (not (name `elem` map getFormName forms1))
             (throwError "Duplicate judgment name")
  wfForms (forms1 ++ [Form name names0]) forms

wfExpr :: [Arity] -> Expr -> Either String Name
wfExpr arities (EVar (Var name nameS)) = return nameS
wfExpr arities (ECon name exprs) = do
  Arity _ names name0 <- maybeToEither ("arity not found: " ++ name)
                         (findArity arities name)
  namesS <- mapM (wfExpr arities) exprs
  unless (namesS == names)
             (throwError $ "constructor applied to wrong arguments: " ++ name ++
             "\narity: " ++ show (Arity name names name) ++
             "\narguments: " ++ show namesS)
  return name0

wfJudg :: [Arity] -> [Form] -> Judg -> Either String ()
wfJudg arities forms (Judg exprs name) = do
  Form _ names <- maybeToEither ("form not found: " ++ name)
                  (findForm forms name)
  namesS <- mapM (wfExpr arities) exprs
  unless (namesS == names)
             (throwError $ "judgment applied to wrong arguments: " ++ name +%+
             show exprs)

wfInfRules :: [Arity] -> [Form] -> [InfRule] -> [InfRule] -> Either String ()
wfInfRules arities forms infRules1 [] = return ()
wfInfRules arities forms infRules1
              (InfRule judgs name judg : infRules) = do
  when (name `elem` map getInfRuleName infRules1)
           (throwError "Duplicate rule name")
  mapM_ (wfJudg arities forms) (judg:judgs)
  wfInfRules arities forms
                    (infRules1++[InfRule judgs name judg]) infRules

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
  let arities = getBaseArities base
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
  wfArities [] arities
  wfForms [] forms

  -- Type system
  wfInfRules arities forms [] infRules

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
