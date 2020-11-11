module Main where

import Data.Map as Map
import Terms
import Types

evaltest1 :: Int -> IO ()
evaltest1 maxnbsteps =
  let x = Let "x" (LInt 5) (Let "y" (Abs "x" (Var "x")) (App (Var "y") (App (App Add (Var "x")) (LInt 5))))
      y = (alphaConv x (Map.fromList []) 1)
      z = eval_CBV (snd y) maxnbsteps ((show (snd y)) : []) (EvalContext (Map.fromList []) (fst y) 1)
   in putStrLn (show z ++ show (typeDetection (snd y)))

evaltest2 :: Int -> IO ()
evaltest2 maxnbsteps =
  let x = App (App Assign (Var "x")) (LInt 5)
      y = (alphaConv x (Map.fromList []) 1)
      z = eval_CBV (snd y) maxnbsteps ((show (snd y)) : []) (EvalContext (Map.fromList []) (fst y) 1)
   in putStrLn (show z)

evaltest3 :: Int -> Int -> IO ()
evaltest3 maxnbsteps v =
  let x = App ((App Fix (Abs "sum" (Abs "x" (IfZ (Var "x") (LInt 0) (App (App Add (Var "x")) (App (Var "sum") (App (App Sub (Var "x")) (LInt 1))))))))) (LInt v)
      y = (alphaConv x (Map.fromList []) 1)
      z = eval_CBV (snd y) maxnbsteps ((show (snd y)) : []) (EvalContext (Map.fromList []) (fst y) 1)
   in do
        putStrLn ("\n\nEvaluation of : " ++ show x)
        printEvalRes z

infertest1 :: () -> IO ()
infertest1 () =
  let x = (App (App Cons (App (App Add (LInt 1)) (LInt 2))) (List []))
   in putStrLn (show $ typeDetection x)

infertest2 :: () -> IO ()
infertest2 () =
  let x = (Let "x" (LInt 5) (Let "y" (Abs "x" (Var "x")) (App (Var "y") (App (App Add (Var "x")) (LInt 5)))))
   in putStrLn (show $ typeDetection x)

infertest3 :: () -> IO ()
infertest3 () =
  let x = App (App Assign (Var "x")) (LInt 5)
   in putStrLn (show $ typeDetection x)

main :: IO ()
main =
  do
    --test1 10
    --test2 10
    --evaltest3 100 5
    infertest1 ()

{-

eval_CBV (App (App Cons (App (App Add (LInt 1)) (LInt 2))) (List [])) 15 [] (makeEvalContext ())

let x =
  (Let "x" (LInt 5)
    (Let "y" (Abs "x" (Var "x"))
      (App (Var "y") ( App (App Add (Var "x")) (LInt 5) ) )
    )
  )
let acx = (alphaConv x (Map.fromList []) 1)
eval_CBV (snd y) 14 (fst y) [] (EvalContext (Map.fromList []) 1)

(["Evaluation End",
"( maxnbsteps = 14, let x1 = 5 in let x3 = \955x2.(x2) in (x3 ( x1 + 5 ))
  -> let x3 = \955x2.(x2) in (x3 ( 5 + 5 )) ) ",

"( maxnbsteps = 13, let x3 = \955x2.(x2) in (x3 ( 5 + 5 ))
  -> (\955x2.(x2) ( 5 + 5 )) ) ",

"( maxnbsteps = 12, (\955x2.(x2) ( 5 + 5 ))
  -> (\955x2.(x2) 10) ) ",

"( maxnbsteps = 11, (\955x2.(x2) 10)
   -> 10 ) "],

10,False)

###############################################################################"
App Fix
  (Abs "sum"
    (Abs "x"
      (IfZ (Var "x") (LInt 0)
        (App
          (App Add (Var "x"))
          (App (Var "sum")
            (App (App Sub (Var "x")) (LInt 1)
            )
          )
        )
      )
    )
  )

App Fix (Abs "sum" (Abs "x" (IfZ (Var "x") (LInt 0) (App (App Add (Var "x")) (App (Var "sum") (App (App Sub (Var "x")) (LInt 1) ))))))

(fix λsum.(λx.(ifZero x then 0 else ( x + (sum ( x - 1 )) ))))"

(["eval_CBV failure: N = 0",
"( maxnbsteps = 1, ((fix \955sum.(\955x.(ifZero x then 0 else ( x + (sum ( x - 1 )) )))) 5)
 -> \955x.(ifZero x then 0 else ( x + (\955x115.(ifZero x115 then 0 else ( x115 + (x116 ( x115 - 1 )) )) ( x - 1 )) )) ) "],λx.(ifZero x then 0 else ( x + (λx115.(ifZero x115 then 0 else ( x115 + (x116 ( x115 - 1 )) )) ( x - 1 )) )),False)

(((fix λsum.(λx.(ifZero x then 0 else ( x + (sum ( x - 1 )) )))) 2) 1)

(λx.(ifZero x then 0 else ( x + (sum ( x - 1 ))
-}

{-
  let x = snd $ alphaConv ((read (replLByLambda "La b.((a b) (b a))" )::LTerm)) (Map.fromList []) 1
      eqs = (snd $ genEquas x (TVar 0) 1 (Map.fromList []))
  in do
    putStrLn ("\n" ++ show x ++ "\n")
    putStrLn ("Generated equations:" ++ show eqs ++ "\n\nEquation solving steps:\n")
    --unifyEqs eqs []
    unifyEqs ((LTypeEqua (TVar 0) (Arrow (TVar 1) (Arrow (TVar 2) (TVar 3)))):(LTypeEqua (TVar 2) (Arrow (TVar 5) (TVar 4))):(LTypeEqua (TVar 1) (TVar 5)):(LTypeEqua (TVar 1) (Arrow (TVar 6) (Arrow (TVar 4) (TVar 3)))):(LTypeEqua (TVar 2) (TVar 6)):[]) []
-}

{-
  let x = (read (replLByLambda "(La.Lb c.(a (b c)) a)" )::LTerm) in
    do
      putStrLn $ show $ x
      putStrLn $ show $ eval_CBV $ x
      putStrLn $ show $ snd $ (alphaConv x (Map.fromList []) 1)
      putStrLn $ show $ eval_CBV $ snd $ (alphaConv x (Map.fromList []) 1)
-}

{-
let x = snd $ alphaConv ((read (replLByLambda "La b.((a b) (b a))" )::LTerm)) (Map.fromList []) 1
let eqs = (snd $ genEquas x (TVar 0) 1 (Map.fromList []))
unify eqs

[∀T3.T3 -> [T3] -> [T3] = T2 -> T1 -> T0,T5 -> T4 -> T2 = ℕ -> ℕ -> ℕ,T5 = ℕ,T4 = ℕ,T1 = [T6]]
[T3 -> T3 -> T3 = T2 -> T1 -> T0,T5 -> T4 -> T2 = ℕ -> ℕ -> ℕ,T5 = ℕ,T4 = ℕ,T1 = [T6]]
[T3 = T2,T3 = T1,T3 = T0,T5 -> T4 -> T2 = ℕ -> ℕ -> ℕ,T5 = ℕ,T4 = ℕ,T1 = [T6]]
[T2 = T1,T2 = T0,T5 -> T4 -> T2 = ℕ -> ℕ -> ℕ,T5 = ℕ,T4 = ℕ,T1 = [T6]]
[T1 = T0,T5 -> T4 -> T1 = ℕ -> ℕ -> ℕ,T5 = ℕ,T4 = ℕ,T1 = [T6]]
[T5 -> T4 -> T1 = ℕ -> ℕ -> ℕ,T5 = ℕ,T4 = ℕ,T1 = [T6],T1 = T0]
[T5 = ℕ,T4 = ℕ,T1 = ℕ,T5 = ℕ,T4 = ℕ,T1 = [T6],T1 = T0]
[T4 = ℕ,T1 = ℕ,ℕ = ℕ,T4 = ℕ,T1 = [T6],T1 = T0]
[T1 = ℕ,ℕ = ℕ,ℕ = ℕ,T1 = [T6],T1 = T0]
[ℕ = ℕ,ℕ = ℕ,ℕ = [T6],ℕ = T0]
[ℕ = ℕ,ℕ = [T6],ℕ = T0]
[ℕ = [T6],ℕ = T0]

[ ℕ = ℕ, ℕ = ℕ, ℕ = ℕ, ℕ = ℕ, [ℕ] = [T6], [ℕ] = T0]

-}