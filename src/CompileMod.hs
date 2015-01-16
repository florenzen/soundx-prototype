module CompileMod where

import WFMod
import Rewrite
import Syntax

compileMod :: Base -> [Intf] -> Mod -> Either String (Expr,Intf)
compileMod base intfs mod = do
    (intf,exts,deriv) <- wfMod intfs base mod
    let expr = desugarMod base exts deriv
    return (expr,intf)
