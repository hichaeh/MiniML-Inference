module Funcs where

import Terms

--import Types

lt_I :: () -> LTerm
lt_I () = Abs "x" (Var "x")

lt_K :: () -> LTerm
lt_K () = Abs "x" (Abs "y" (Var "x"))

lt_S :: () -> LTerm
lt_S () = Abs "x" (Abs "y" (Abs "z" (App (App (Var "x") (Var "z")) (App (Var "y") (Var "z")))))

lt_D :: () -> LTerm
lt_D () = Abs "x" (App (Var "x") (Var "x"))

lt_sum_0toN :: () -> LTerm
lt_sum_0toN () =
  App Fix (Abs "sum" (Abs "x" (IfZ (Var "x") (LInt 0) (App (App Add (Var "x")) (App (Var "sum") (App (App Sub (Var "x")) (LInt 1)))))))

lt_sum_0toN_App :: Int -> LTerm
lt_sum_0toN_App n =
  App ((App Fix (Abs "sum" (Abs "x" (IfZ (Var "x") (LInt 0) (App (App Add (Var "x")) (App (Var "sum") (App (App Sub (Var "x")) (LInt 1))))))))) (LInt n)
