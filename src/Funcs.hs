module Funcs where

import Terms

testI :: () -> LTerm
testI () = Abs "x" (Var "x")

testA :: () -> LTerm
testA () = Abs "x" (Abs "y" (App (Var "x") (Var "y")))

testK :: () -> LTerm
testK () = Abs "x" (Abs "y" (Var "x"))

testS :: () -> LTerm
testS () = Abs "x" (Abs "y" (Abs "z" (App (App (Var "x") (Var "z")) (App (Var "y") (Var "z")))))

testSKK :: () -> LTerm
testSKK () = App (App (testS ()) (testK ())) (testK ())

testSIII :: () -> LTerm
testSIII () = App (App (App (testS ()) (testI ())) (testI ())) (testI ())

testDelta :: () -> LTerm
testDelta () = Abs "x" (App (Var "x") (Var "x"))

testOmega :: () -> LTerm
testOmega () = App (testDelta ()) (testDelta ())

testKIOm :: () -> LTerm
testKIOm () = App (App (testK ()) (testI ())) (testOmega ())

testCons123 :: () -> LTerm
testCons123 () =
  App (App Cons (LInt 1)) (App (App Cons (LInt 2)) (App (App Cons (LInt 3)) (List [])))

testMap :: () -> LTerm
testMap () =
  let x1 = App (Var "f") (App Hd (Var "l"))
      x2 = App (App (Var "map") (Var "f")) (App Tl (Var "l"))
   in App Fix (Abs "map" (Abs "f" (Abs "l" (IfE (Var "l") (List []) (App (App Cons x1) x2)))))

testMapApp :: LTerm -> [LTerm] -> LTerm
testMapApp func list =
  App (App (testMap ()) func) (List list)

testSum0toN :: () -> LTerm
testSum0toN () =
  App Fix (Abs "sum" (Abs "x" (IfZ (Var "x") (LInt 0) (App (App Add (Var "x")) (App (Var "sum") (App (App Sub (Var "x")) (LInt 1)))))))

testSum0toNApp :: Int -> LTerm
testSum0toNApp n =
  App (App Fix (Abs "sum" (Abs "x" (IfZ (Var "x") (LInt 0) (App (App Add (Var "x")) (App (Var "sum") (App (App Sub (Var "x")) (LInt 1)))))))) (LInt n)

testLetLetMap :: () -> LTerm
testLetLetMap () =
  Let "x" (App (App Add (LInt 2)) (LInt 3)) (Let "y" (Abs "z" (App (App Add (Var "x")) (Var "z"))) (App (App (testMap ()) (Var "y")) (List [LInt 1, LInt 2, LInt 3])))

testLetRefDerefAssign :: () -> LTerm
testLetRefDerefAssign () =
  Let "l" (App Ref (List [])) (Let "_" (App (App Assign (Var "l")) (List [LInt 123])) (App Deref (Var "l")))

testRefDerefAssign :: () -> LTerm
testRefDerefAssign () =
  Let "l" (App Ref (List [LInt 2])) (App (App Assign (Var "l")) (App (App Cons (LInt 1)) (App Deref (Var "l"))))

-- Doesn't Evaluate :  let l = (ref []) in let _ = ( l:=( λx.(x)::!l ) ) in ( (hd !l) + 8 )  ->  (λx.(x) + 8)
testExp1 :: () -> LTerm
testExp1 () =
  Let "l" (App Ref (List [])) (Let "_" (App (App Assign (Var "l")) (App (App Cons (testI ())) (App Deref (Var "l")))) (App (App Add (App Hd (App Deref (Var "l")))) (LInt 8)))

-- Evaluates :  let l = (ref []) in let _ = ( l:=( λx.(x)::!l ) ) in ( (hd !l) + 8 )  ->  ( (λx.(x) 5) + 8) -> ( 5 + 8 ) -> 13
testExp2 :: () -> LTerm
testExp2 () =
  Let "l" (App Ref (List [])) (Let "_" (App (App Assign (Var "l")) (App (App Cons (testI ())) (App Deref (Var "l")))) (App (App Add (App (App Hd (App Deref (Var "l"))) (LInt 5))) (LInt 8)))