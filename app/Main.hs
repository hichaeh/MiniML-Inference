module Main where

--import Data.Map as Map

import Evaluation
import Funcs
import Terms
import TypeInference

doEval :: LTerm -> Int -> IO ()
doEval lte maxnbsteps =
  print $ evalCBV lte maxnbsteps

doType :: LTerm -> IO ()
doType lte = print $ typeInference lte

main :: IO ()
main =
  do
    --  putStrLn ""

    doType (testKIOm ())
    doEval (testKIOm ()) 250

    doType (testCons123 ())
    doEval (testCons123 ()) 250

    doType (testSum0toN ())
    doEval (testSum0toN ()) 250

    doType (testSum0toNApp 5)
    doEval (testSum0toNApp 5) 250

    doType (testMapApp (App Add (LInt 5)) [LInt 1, LInt 2, LInt 3])
    doEval (testMapApp (App Add (LInt 5)) [LInt 1, LInt 2, LInt 3]) 1234

    doType (testLetLetMap ())
    doEval (testLetLetMap ()) 1234

    doType (testRefDerefAssign ())
    doEval (testRefDerefAssign ()) 1234

    doType (testExp1 ())

    doEval (testExp1 ()) 1234

    doType (testExp2 ())

    doEval (testExp2 ()) 1234
