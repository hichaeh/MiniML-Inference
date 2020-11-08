
module Terms where

import Data.Map as Map 
import Data.List as List

data LTerm = 
  Var String
  | App LTerm LTerm
  | Abs String LTerm
  
  | LInt Int
  | List [LTerm]
  
  | Let String LTerm LTerm
  | IfZ LTerm LTerm LTerm
  | IfE LTerm LTerm LTerm

  -- App (App Op Int) Int
  | Add
  | Sub  
  -- App (App Op Var) (List Var)
  | Cons 
  -- App Op (List Var)
  | Hd 
  | Tl 
  
  -- App Op (Abs)
  | Fix  

--  | LTRef String LTerm
  | Unit deriving Eq

--  | Assign String LTerm
--  | Deref LTerm deriving Eq


cons :: LTerm -> [LTerm] -> [LTerm]
cons hd tl = hd:tl

instance Show LTerm where
  show (Var x) = x
  show (Abs x y) = 
    "λ" ++ x ++ ".(" ++ (show y) ++ ")" 

  show (LInt x) = 
    show x
  show (List l) = 
    List.intercalate ", " (List.map show l)
  
  show (Let x y z) =
    "let " ++ x ++ " = " ++ (show y) ++ " in " ++ (show z)
  show (IfZ x y z) =
    "ifZero " ++ (show x) ++ " then " ++ (show y) ++ " else " ++ (show z)
  show (IfE x y z) =
    "ifEmpty " ++ (show x) ++ " then " ++ (show y) ++ " else " ++ (show z)

  show Add = " + "
  show Sub = " - "
  show Cons = "::"
  show Hd = "hd"
  show Tl = "tl"
  show Fix = "fix"

  show (App (App Add x) y) =  "( " ++ (show x) ++ (show Add) ++ (show y)  ++ " )"
  show (App (App Sub x) y)  = "( " ++ (show x) ++ (show Sub) ++ (show y)  ++ " )"
  show (App (App Cons x) y) = "( " ++ (show x) ++ (show Cons) ++ (show y) ++ " )"

  show (App Add x)  = (show x) -- ++ (show Add)
  show (App Sub x)  = (show x) -- ++ (show Sub)
  show (App Cons x) = (show x) -- ++ (show Cons)

  show Unit = "□"
  show (App x y) = "(" ++ (show x) ++ " " ++ (show y) ++ ")"

alphaConvList :: [LTerm] -> Map String String -> Int -> [LTerm] ->  (Int, [LTerm])
alphaConvList ((Var str):tl) context n acc =
  case (Map.lookup str context) of
    Just x -> alphaConvList tl context n ((Var x):acc)
    Nothing -> alphaConvList tl (Map.insert str ("x"++(show n)) context) (n+1) ((Var ("x"++(show n))):acc)

alphaConvList (hd:tl) context n acc = 
  let (newN, newLT) = (alphaConv hd context n) in
    alphaConvList tl context newN (newLT:acc)

alphaConvList [] _ n acc = (n, List.reverse acc)


alphaConv :: LTerm -> Map String String -> Int -> (Int, LTerm)
alphaConv (Var v) context n = 
  case Map.lookup v context of
    Just x -> (n, Var x)
    Nothing -> (n + 1, Var ("x" ++ show n))
alphaConv (Abs var body) context n =
  let newContext = Map.insert var ("x" ++ show n) context in
  let (newN, newLTe) = alphaConv body newContext (n+1) in
    (newN, Abs ("x" ++ show n) newLTe)
alphaConv (App lterm1 lterm2) context n =
  let (newN1, newLterm1) = alphaConv lterm1 context n in
  let (newN2, newLterm2) = alphaConv lterm2 context newN1 in
    (newN2, App newLterm1 newLterm2)
alphaConv (List l) context n = 
  let (newN, newL) = (alphaConvList l context n []) in
    (newN, List newL)

alphaConv (Let str lte1 lte2) context n =
  let (newN1, newLTe1) = alphaConv lte1 newContext n
      newVStr = "x" ++ show newN1
      newContext = (Map.insert str newVStr context)
      (newN2, newLTe2) = alphaConv lte2 newContext (newN1 + 1)
  in
    (newN2, Let newVStr newLTe1 newLTe2)  

alphaConv (IfZ lte1 lte2 lte3) context n =
  let (newN1, newLTe1) = (alphaConv lte1 context n) in
  let (newN2, newLTe2) = (alphaConv lte2 context newN1) in
  let (newN3, newLTe3) = (alphaConv lte3 context newN2) in
    (newN3 ,IfZ newLTe1 newLTe2 newLTe3)

alphaConv (IfE lte1 lte2 lte3) context n =
  let (newN1, newLTe1) = (alphaConv lte1 context n) in
  let (newN2, newLTe2) = (alphaConv lte2 context newN1) in
  let (newN3, newLTe3) = (alphaConv lte3 context newN2) in
    (newN3 ,IfE newLTe1 newLTe2 newLTe3)

alphaConv x _ n = (n, x)


instantiate :: String -> LTerm -> LTerm -> LTerm 
instantiate varToRep newLT (Var x) 
  | x == varToRep = newLT
  | otherwise = Var x
instantiate varToRep newLT (App lt1 lt2) = 
  App (instantiate varToRep newLT lt1) (instantiate varToRep newLT lt2)
instantiate varToRep newLT (Abs var body) =
  Abs var (instantiate varToRep newLT body)

instantiate varToRep newLT (IfZ lte1 lte2 lte3) = 
  IfZ (instantiate varToRep newLT lte1) (instantiate varToRep newLT lte2)  (instantiate varToRep newLT lte3) 

instantiate varToRep newLT (IfE lte1 lte2 lte3) = 
  IfE (instantiate varToRep newLT lte1) (instantiate varToRep newLT lte2)  (instantiate varToRep newLT lte3) 

instantiate varToRep newLT (Let v lte1 lte2) = 
  Let v (instantiate varToRep newLT lte1) (instantiate varToRep newLT lte2) 

instantiate varToRep newLT (List l) =
  List (List.map (instantiate varToRep newLT) l)


-- ?????
--instantiate varToRep newLT (Fix phi lte) =
--   Fix phi (instantiate varToRep newLT lte)
instantiate _ _ x = x


data EvalStepRes = EvalStepSuccess LTerm Int | EvalStepFailure LTerm String 

getEvalStr :: String -> String -> String
getEvalStr oldterm newterm =
  "( " ++ oldterm ++ " -> " ++ newterm ++ " )"

evalApp :: LTerm -> LTerm -> Int -> EvalStepRes
evalApp (Abs v body) arg n =
  EvalStepSuccess (instantiate v arg body) n

evalApp (App Hd (List (x:_))) _ n =
  EvalStepSuccess x n
evalApp (App Tl (List (_:xs))) _ n =
  EvalStepSuccess (List xs) n

evalApp (App Add (LInt arg1)) (LInt arg2) n = 
  EvalStepSuccess (LInt (arg1 + arg2)) n

evalApp (App Sub (LInt arg1)) (LInt arg2) n = 
  EvalStepSuccess (LInt (arg1 - arg2)) n

evalApp (App Cons arg1) (List arg2) n = 
  EvalStepSuccess (List (arg1:arg2)) n

evalApp (App Fix (Abs v body)) _ n =
  let (newN, newLTy) = alphaConv body (Map.fromList []) n in
  EvalStepSuccess (instantiate v newLTy body) newN

evalApp f a _ = EvalStepFailure (App f a) "evalApp : unevaluable"

eval_CBV_step :: LTerm -> Int -> EvalStepRes  
eval_CBV_step (App lte1 lte2) n =
  case (eval_CBV_step lte1 n) of
    EvalStepSuccess newLTe1 newN -> EvalStepSuccess (App newLTe1 lte2) newN
    EvalStepFailure _ _ ->(
      case (eval_CBV_step lte2 n) of
        EvalStepSuccess newLTe2 newN -> EvalStepSuccess (App lte1 newLTe2) newN
        EvalStepFailure _ _ -> evalApp lte1 lte2 n)

--data EvalStepRes = EvalStepSuccess LTerm | EvalStepFailure LTerm String 

eval_CBV_step (Let x lte1 lte2) n =
  case (eval_CBV_step lte1 n) of
    EvalStepSuccess newLTe1 newN ->
      EvalStepSuccess (Let x newLTe1 lte2) newN
    EvalStepFailure _ _ -> 
      let newLTe2 = instantiate x lte1 lte2 in
        EvalStepSuccess newLTe2 n

eval_CBV_step (IfZ lte1 lte2 lte3) n =
  case (eval_CBV_step lte1 n) of
    EvalStepSuccess newLTe1 newN -> EvalStepSuccess (IfZ newLTe1 lte2 lte3) newN
    EvalStepFailure _ _ ->
      case lte1 of 
        LInt x -> if x == 0 
          then (EvalStepSuccess lte2 n) 
          else (EvalStepSuccess lte3 n)
        _ -> EvalStepFailure (IfZ lte1 lte2 lte3) "Eval failure ifz" 
{-
  let (newLTe1, b) = eval_CBV_step lte1 in
  if b == True then 
    ((IfZ newLTe1 lte2 lte3), True)
  else
    case newLTe1 of 
      LInt x -> 
        if x == 0 
          then (lte2, True)
          else (lte3, True)
      _ ->  (IfZ newLTe1 lte2 lte3, False)
-}

eval_CBV_step (IfE lte1 lte2 lte3) n =
  case (eval_CBV_step lte1 n) of
    EvalStepSuccess newLTe1 newN -> EvalStepSuccess (IfZ newLTe1 lte2 lte3) newN
    EvalStepFailure _ _ ->
      case lte1 of 
        LInt x -> if x == 0 
          then (EvalStepSuccess lte2 n) 
          else (EvalStepSuccess lte3 n)
        _ -> EvalStepFailure (IfZ lte1 lte2 lte3) "Eval failure ifz"

eval_CBV_step lte _ = EvalStepFailure lte "Evaluation Over"

eval_CBV :: LTerm -> Int -> Int -> [String] -> ([String], LTerm, Bool)
eval_CBV lte gas n acc 
  | gas > 0 =
    case (eval_CBV_step lte n) of
      EvalStepSuccess newLTe newN -> 
        eval_CBV newLTe (gas-1) newN (("( gas = " ++ (show gas ) ++ ", "++ (show lte) 
        ++ " -> " ++ (show newLTe) ++ " ) "):acc)
      EvalStepFailure newLTe msg -> (msg:(List.reverse acc), newLTe, False)
  | otherwise = ("eval_CBV failure: N = 0":(List.reverse acc), lte, False)

