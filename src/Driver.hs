module Driver where

-- import Debug.Trace
import Control.Monad
import qualified Data.Set as S
import Prelude hiding (mod)

import Syntax
import qualified Derive as D
import Rewrite
import Validation
import qualified Verification as V
import WFMod
import qualified CompileMod as C

compileMod :: Bool -> Base -> [Intf] -> Mod -> IO ()
compileMod tex base intfs mod = do
  case C.compileMod base intfs mod of
    Left msg ->  putStrLn $ "ERROR:\n" ++ msg
    Right (expr,intf) -> do
      case wfMod intfs base (Mod expr extEmpty) of
        Left msg -> putStrLn $ "ERROR: resulting module not well-formed\n" ++ msg
        Right (intf,exts,deriv) -> do
           putStrLn $ "OK: resulting module well-formed"
           if validate [] (getBaseInfRules base) deriv then do
               putStrLn $ "OK:\n" ++
                 "Desugared code:\n" ++ show expr ++
                 "Interface:\n" ++ show intf
               when tex (teXDerivations "deriv" [Asm (Judg [expr] "")])
            else
                putStrLn $ "ERROR: derivation of resulting module not valid"

deriveMod :: Bool -> Base -> [Intf] -> Mod -> IO ()
deriveMod tex base intfs mod =
    case wfMod intfs base mod of
      Left msg -> putStrLn $ "ERROR:\n" ++ msg
      Right (intf,exts,deriv) -> do
          putStrLn $ "OK:\n" ++
                   "Interface:\n" ++ show intf ++
                   "Derivation:\n" ++ show deriv
          when tex (teXDerivations "deriv" [deriv])

derive :: Bool -> [Ext] -> Base -> Judg -> IO ()
derive tex exts base judg =
    let infRulesX = concatMap getExtInfRules exts
        infRules = getBaseInfRules base
    in case D.derive [] (infRulesX ++ infRules) [judg] (varsJudg judg) of
         Left msg ->
           putStrLn $ "ERROR:\n" ++ show msg
         Right [deriv] -> do
           putStrLn $ "OK:\n" ++ show (concl deriv)
           when tex (teXDerivations "deriv" [deriv])

deriveDesugar :: Bool -> [Ext] -> Base -> Judg -> IO ()
deriveDesugar tex exts base judg =
    let infRulesX = concatMap getExtInfRules exts
        infRules = getBaseInfRules base
        infRulesAll = infRulesX ++ infRules in
    case D.derive [] infRulesAll [judg] (varsJudg judg) of
      Left msg ->
          putStrLn $ "ERROR:\n" ++ show msg
      Right [deriv] -> do
        putStrLn $ "OK:\n" ++ show (concl deriv)
        let deriv' = desugar base exts deriv
        putStrLn $ "*** successfully rewritten:\n" ++ show (concl deriv')
        let deriveResult = D.derive [] infRules [concl deriv']
                           S.empty
        case deriveResult of
          Left msg -> putStrLn "!!! CANNOT DERIVE DESUGARING RESULT IN B !!!"
          Right [deriv1] -> do
                    putStrLn "*** succssfully derived desugaring result"
                    when (deriv1 /= deriv')
                         (putStrLn $ "(BUT DERIVATIONS DIFFER:\n1" ++
                                   show (concl deriv1) ++ ")")
                    if validate [] infRules deriv' then
                        putStrLn "*** desugaring result valid"
                     else
                         putStrLn "!!! DESUGARING RESULT INVALID !!!"
                    when tex (teXDerivations "deriv" [deriv,deriv',deriv1])

verify :: Ext -> [Ext] -> Base -> IO ()
verify ext exts base = do
  case V.verify base exts ext of
      Right () ->
          putStrLn $ "*** extension verified"
      Left msg ->
          putStrLn $ "!!! EXTENSION  NOT VERIFIED:\n" ++ msg
