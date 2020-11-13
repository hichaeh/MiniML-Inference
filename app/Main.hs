module Main where

--import Data.Map as Map
import Funcs
import Terms
import Types

doEval :: LTerm -> Int -> IO ()
doEval lte maxnbsteps =
  print $ evalCBV lte maxnbsteps

doType :: LTerm -> IO ()
doType lte = print $ typeInference lte

main :: IO ()
main =
  do
    --doType (testKIOm ())
    --doEval (testKIOm ()) 250

    --doType (testCons123 ())
    --doEval (testCons123 ()) 250

    --doType (testSum0toN ())
    --doEval (testSum0toN ()) 250

    --doType (testSum0toNApp 5)
    --doEval (testSum0toNApp 5) 250

    --doType (testMapApp (App Add (LInt 5)) [LInt 1, LInt 2, LInt 3])
    --doEval (testMapApp (App Add (LInt 5)) [LInt 1, LInt 2, LInt 3]) 1234

    --doType (testLetLetMap ())
    --doEval (testLetLetMap ()) 1234

    --doType (testRefDerefAssign ())
    --doEval (testRefDerefAssign ()) 1234
    --let x = Let "l" (App Ref (List [])) (Let "_" (App (App Assign (Var "l")) (App (App Cons (testI ())) (App Deref (Var "l")))) (App (App Add (App Hd (App Deref (Var "l")))) (LInt 8)))
    --    let x = Let "l" (App Ref (List [])) (Let "_" (App (App Assign (Var "l")) (App (App Cons (testI ())) (App Deref (Var "l")))) (App (App Add (App Hd (App Deref (Var "l")))) (LInt 8)))
    --     in do
    --          doType x
    --          doEval x 1234

    let y = Let "l" (App Ref (List [])) (Let "_" (App (App Assign (Var "l")) (App (App Cons (testI ())) (App Deref (Var "l")))) (App (App Add (App (App Hd (App Deref (Var "l"))) (LInt 5))) (LInt 8)))
     in do
          doType y
          doEval y 1234

    doType (testLetMem ())
    doEval (testLetMem ()) 1234

-- let l = (ref []) in let _ = ( l:=( λx.(x)::!l ) ) in ( (hd !l) + 8 )
-- let l = (ref []) in let _ = ( l:=( λx.(x)::!l ) ) in ( (App (hd !l) (LInt 5)) + 8 )
{-

0 | let l = (ref []) in let _ = ( l:=( λx.(x)::!l ) ) in ( (hd !l) + 8 )
1 | let l = p:1 in let _ = ( l:=( λx.(x)::!l ) ) in ( (hd !l) + 8 )
2 | let _ = ( p:1:=( λx.(x)::!p:1 ) ) in ( (hd !p:1) + 8 )
3 | let _ = ( p:1:=( λx.(x)::[] ) ) in ( (hd !p:1) + 8 )
4 | let _ = ( p:1:=[λx.(x)] ) in ( (hd !p:1) + 8 )
5 | let _ = □ in ( (hd !p:1) + 8 )
6 | ( (hd !p:1) + 8 )
7 | ( (hd [λx.(x)]) + 8 )
8 | ( λx.(x) + 8 )

-}