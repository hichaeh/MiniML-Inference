module Funcs where

import Terms

-- | λx.(x)
testI :: () -> LTerm
testI () =
  Abs "x" (Var "x")

-- | λx.(λy.((x y)))
testA :: () -> LTerm
testA () =
  Abs "x" (Abs "y" (App (Var "x") (Var "y")))

-- | λx.(λy.(x))
testK :: () -> LTerm
testK () =
  Abs "x" (Abs "y" (Var "x"))

-- | λx.(λy.(λz.(((x z) (y z)))))
testS :: () -> LTerm
testS () =
  Abs "x" (Abs "y" (Abs "z" (App (App (Var "x") (Var "z")) (App (Var "y") (Var "z")))))

-- | ((λx.(λy.(λz.(((x z) (y z))))) λx.(λy.(x))) λx.(λy.(x)))
testSKK :: () -> LTerm
testSKK () =
  App (App (testS ()) (testK ())) (testK ())

-- | (((λx.(λy.(λz.(((x z) (y z))))) λx.(x)) λx.(x)) λx.(x))
testSIII :: () -> LTerm
testSIII () =
  App (App (App (testS ()) (testI ())) (testI ())) (testI ())

-- | λx.((x x))
testDelta :: () -> LTerm
testDelta () =
  Abs "x" (App (Var "x") (Var "x"))

-- | (λx.((x x)) λx.((x x)))
testOmega :: () -> LTerm
testOmega () =
  App (testDelta ()) (testDelta ())

-- | ((λx.(λy.(x)) λx.(x)) (λx.((x x)) λx.((x x))))
testKIOm :: () -> LTerm
testKIOm () =
  App (App (testK ()) (testI ())) (testOmega ())

{-
  ( 1::( 2::( 3::[] ) ) )
  Type: [TInt]
  Eval: [1, 2, 3]
-}
testCons123 :: () -> LTerm
testCons123 () =
  App (App Cons (LInt 1)) (App (App Cons (LInt 2)) (App (App Cons (LInt 3)) (List [])))

{-
  (fix λmap.(λf.(λl.(ifEmpty l then [] else ( (f (hd l))::((map f) (tl l)) )))))
  Type: ( T6 -> T8 ) -> ( [T6] -> [T8] ) )     map: T6 -> T8,  l (list): [T6], result [T8]
  Eval: unevaluable
-}
testMap :: () -> LTerm
testMap () =
  App Fix (Abs "map" (Abs "f" (Abs "l" (IfE (Var "l") (List []) (App (App Cons (App (Var "f") (App Hd (Var "l")))) (App (App (Var "map") (Var "f")) (App Tl (Var "l"))))))))

{-
  With: testMapApp (App Add (LInt 5)) (testCons123 ())
  (((fix λmap.(λf.(λl.(ifEmpty l then [] else ( (f (hd l))::((map f) (tl l)) ))))) (+) 5) [1, 2, 3])
  Type: [ℕ]           [TInt]
  Eval: [6, 7, 8]
-}
testMapApp :: LTerm -> [LTerm] -> LTerm
testMapApp func list =
  App (App (testMap ()) func) (List list)

{-
  (fix λsum.(λx.(ifZero x then 0 else ( x + (sum ( x - 1 )) ))))
  Type: ( ℕ -> ℕ )
  Eval: unevaluable
-}
testSum0toN :: () -> LTerm
testSum0toN () =
  App Fix (Abs "sum" (Abs "x" (IfZ (Var "x") (LInt 0) (App (App Add (Var "x")) (App (Var "sum") (App (App Sub (Var "x")) (LInt 1)))))))

{-
  With: testSum0toNApp 5
  ((fix λsum.(λx.(ifZero x then 0 else ( x + (sum ( x - 1 )) )))) 5)
  Type: ℕ
  Eval: 15
-}
testSum0toNApp :: Int -> LTerm
testSum0toNApp n =
  App (App Fix (Abs "sum" (Abs "x" (IfZ (Var "x") (LInt 0) (App (App Add (Var "x")) (App (Var "sum") (App (App Sub (Var "x")) (LInt 1)))))))) (LInt n)

{-
  let x = ( 2 + 3 ) in let y = λz.(( x + z )) in (((fix λmap.(λf.(λl.(ifEmpty l then [] else ( (f (hd l))::((map f) (tl l)) ))))) y) [1, 2, 3])
  Type: [ℕ]
  Eval: [6, 7, 8]
-}
testLetLetMap :: () -> LTerm
testLetLetMap () =
  Let "x" (App (App Add (LInt 2)) (LInt 3)) (Let "y" (Abs "z" (App (App Add (Var "x")) (Var "z"))) (App (App (testMap ()) (Var "y")) (List [LInt 1, LInt 2, LInt 3])))

{-
  let l = (ref []) in let _ = ( l:=[123] ) in !l
  Type: [_T3]
  Eval: [123]
-}
testLetRefDerefAssign :: () -> LTerm
testLetRefDerefAssign () =
  Let "l" (App Ref (List [])) (Let "_" (App (App Assign (Var "l")) (List [LInt 123])) (App Deref (Var "l")))

{-
  let l = (ref [2]) in ( l:=( 1::!l ) )
  Type: ⬤
  Eval: □
-}
testRefDerefAssign :: () -> LTerm
testRefDerefAssign () =
  Let "l" (App Ref (List [LInt 2])) (App (App Assign (Var "l")) (App (App Cons (LInt 1)) (App Deref (Var "l"))))

{-
  let l = (ref []) in let _ = ( l:=( λx.(x)::!l ) ) in ( (hd !l) + 8 )
  Type: Unification failure ℕ is incompatible with ( T7 -> T7 )
  Eval: The evaluation failed! cause : [[[failcause : 3.2]]]   (unevaluable ( λx.(x) + 8 ))
-}
testExp1 :: () -> LTerm
testExp1 () =
  Let "l" (App Ref (List [])) (Let "_" (App (App Assign (Var "l")) (App (App Cons (testI ())) (App Deref (Var "l")))) (App (App Add (App Hd (App Deref (Var "l")))) (LInt 8)))

{-
  let l = (ref []) in let _ = ( l:=( λx.(x)::!l ) ) in ( ((hd !l) 5) + 8 )
  Type: ℕ
  Eval: 13
-}
testExp2 :: () -> LTerm
testExp2 () =
  Let "l" (App Ref (List [])) (Let "_" (App (App Assign (Var "l")) (App (App Cons (testI ())) (App Deref (Var "l")))) (App (App Add (App (App Hd (App Deref (Var "l"))) (LInt 5))) (LInt 8)))
