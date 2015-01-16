module Forward where

import           Data.Either.Utils
import qualified Data.List as L
import qualified Data.Set as S

import           Freshening
import           Substitution
import           Syntax
import           Unification


forward :: Base -> [Deriv] -> ([Judg], Judg) -> Deriv -> Either String Deriv
forward base derivsAsm p deriv = do
    (_,d) <- forward1 base derivsAsm p deriv
    return d


-- Problem with this approach:
-- substitution must be applied to subderivations. This is expensive.
-- It should be possible to use an approach like in forwardQuick (see
-- below), which is not yet working.
-- But this "blueprint forward step" requires many changes to the
-- existing (topdown/bottomup) formalization and the blueprint step
-- is also quite complicated. It seems to be relatively straight to
-- proof that it generated valid derivations (see handwritten notes
-- in "blueprint-statement.pdf")
forward1 :: Base -> [Deriv] -> ([Judg],Judg) -> Deriv
         -> Either String (Sub, Deriv)
forward1 base derivsAsm (judgs',judg') (Asm judg) = do
  i <- maybeToEither ("forward1: assumption not in premises")
         (L.elemIndex judg judgs')
  return (emptySub, derivsAsm !! i)
forward1 base derivsAsm (judgs',judg') (Deriv derivs name judg) = do
  let infRules = getBaseInfRules base
  infRule <- maybeToEither ("rule not found")
             (findInfRule infRules name)
  res <- mapM (forward1 base derivsAsm (judgs',judg')) derivs
  let derivs1 = map snd res
  -- (sub1,derivs1) <- forwardList base derivsAsm (judgs',judg') derivs []
  let judgs1 = map concl derivs1
      (_, InfRule judgsIR nameIR judgIR) =
                       freshInfRule (varsDerivs derivs1 `S.union` varsJudg judg) infRule
  sub1 <- -- trace ("rule    " ++ nameIR ++
          --       "\nJudgs1  " ++ show judgs1 ++
          --       "\nJudgsIR " ++ show judgsIR ++
          --       "\nDerivA  " ++ show derivs1 ++
          --       "\nBluepr  " ++ show (Deriv derivs name judg)) $
         unifyJudgs (varsJudgs (judgsIR) `S.union` varsJudgs (judgs1))
                        (zip (judgs1) (judgsIR))
  sub2 <- -- trace ("judgIR: " ++ show judgIR ++
          --        "\njudg:   " ++ show judg) $
          unifyJudg (varsJudg judgIR) judgIR judg
  let sub21 = restrictSub sub2 (domSub sub2 `S.difference`
                                      varsJudgs judgsIR)
  let sub = sub21 `composeSub` sub1
      judg1 = applySubJudg sub judgIR
      derivs2 = applySubDerivs sub derivs1
      derivResult = Deriv derivs2 name judg1
  return $ -- trace ("Result " ++ show derivResult)
             (sub `composeSub` sub1, derivResult)




forwardQuick :: Base -> [Deriv] -> ([Judg], Judg) -> Deriv -> Either String Deriv
forwardQuick base derivsAsm p deriv = do
    (sub1,deriv1) <- forwardQuick1 base derivsAsm p deriv
    return (forwardQuick2 sub1 (deriv,deriv1))


forwardQuick1 :: Base -> [Deriv] -> ([Judg],Judg) -> Deriv
         -> Either String (Sub, Deriv)
forwardQuick1 base derivsAsm (judgs',judg') (Asm judg) = do
  i <- maybeToEither ("forward1: assumption not in premises")
         (L.elemIndex judg judgs')
  return (emptySub, derivsAsm !! i)
forwardQuick1 base derivsAsm (judgs',judg') (Deriv derivs name judg) = do
  let infRules = getBaseInfRules base
  infRule <- maybeToEither ("rule not found")
             (findInfRule infRules name)
  res <- mapM (forwardQuick1 base derivsAsm (judgs',judg')) derivs
  let derivs1 = map snd res
  -- (sub1,derivs1) <- forwardList base derivsAsm (judgs',judg') derivs []
  let judgs1 = map concl derivs1
      (_, InfRule judgsIR nameIR judgIR) =
                       freshInfRule (varsDerivs derivs1 `S.union` varsJudg judg) infRule
  sub1 <- -- trace ("rule    " ++ nameIR ++
          --       "\nJudgs1  " ++ show judgs1 ++
          --       "\nJudgsIR " ++ show judgsIR ++
          --       "\nDerivA  " ++ show derivs1 ++
          --       "\nBluepr  " ++ show (Deriv derivs name judg)) $
         unifyJudgs (varsJudgs (judgsIR))
                        (zip (judgs1) (judgsIR))
  -- sub2 <- -- trace ("judgIR: " ++ show judgIR ++
  --         --        "\njudg:   " ++ show judg) $
  --         unifyJudg (varsJudg judgIR) judgIR judg
  -- let sub21 = restrictSub sub2 (domSub sub2 `S.difference`
  --                                     varsJudgs judgsIR)
  let -- sub = sub21 `composeSub` sub1
      judg1 = applySubJudg sub1 judgIR
      derivs2 = derivs1 -- applySubDerivs sub derivs1
      derivResult = Deriv derivs2 name judg1
  return $ -- trace ("Result " ++ show derivResult)
             (sub1 `composeSub` foldl composeSub emptySub (map fst res), derivResult)

forwardQuick2 :: Sub -> (Deriv, Deriv) -> Deriv
forwardQuick2 sub (Deriv [] _ _, Deriv [] name judgC) =
    Deriv [] name (applySubJudg sub judgC)
forwardQuick2 sub (Deriv derivs _ _, Deriv derivsP name judgC) =
    let derivs' = map (forwardQuick2 sub) (zip derivs derivsP)
    in Deriv derivs' name (applySubJudg sub judgC)
