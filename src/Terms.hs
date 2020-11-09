
module Terms where

import Data.Map as Map 
import Data.List as List

data LTerm = 
  Var String
  | App LTerm LTerm
  | Abs String LTerm
  
  | IfZ LTerm LTerm LTerm
  | IfE LTerm LTerm LTerm
  | Let String LTerm LTerm

  | LInt Int
  | List [LTerm]

  | Vaddr String
  | Unit

  | Add 
  | Sub 
  
  | Cons 
  | Hd    
  | Tl    
  
  | Fix

  | Ref    
  | Deref 
  | Assign deriving Eq

--data OpBin = Fix2 | Assign2 | Sub2 | Add2 | Cons2
--data OpUn = Ref2 | Deref2 | Hd | Tl



cons :: LTerm -> [LTerm] -> [LTerm]
cons hd tl = hd:tl

instance Show LTerm where
  show (Var x) = x
  show (Abs x y) =  "λ" ++ x ++ ".(" ++ (show y) ++ ")" 

  show (LInt x) = show x
  show (List l) = List.intercalate ", " (List.map show l)
  
  show (Let x y z) = "let " ++ x ++ " = " ++ (show y) ++ " in " ++ (show z)
  show (IfZ x y z) = "ifZero " ++ (show x) ++ " then " ++ (show y) ++ " else " ++ (show z)
  show (IfE x y z) = "ifEmpty " ++ (show x) ++ " then " ++ (show y) ++ " else " ++ (show z)

  show Add = " + "
  show Sub = " - "
  show Cons = "::"
  show Hd = "hd"
  show Tl = "tl"
  show Fix = "fix"
  show Ref = "ref"
  show Deref = "!"
  show Assign = ":="

  show (Vaddr str) = str

  show (App (App Add x) y)  = "( " ++ (show x) ++ (show Add) ++ (show y)  ++ " )"
  show (App (App Sub x) y)  = "( " ++ (show x) ++ (show Sub) ++ (show y)  ++ " )"
  show (App (App Cons x) y) = "( " ++ (show x) ++ (show Cons) ++ (show y) ++ " )"

  show (App Deref x) = "!" ++ (show x)
  show (App (App Assign x) y) = "( " ++ (show x) ++ (show Assign) ++ (show y) ++ " )"

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
alphaConv (Let str lte1 lte2) context n =
  let (newN1, newLTe1) = alphaConv lte1 newContext n
      newVStr = "x" ++ show newN1
      newContext = (Map.insert str newVStr context)
      (newN2, newLTe2) = alphaConv lte2 newContext (newN1 + 1)
  in
    (newN2, Let newVStr newLTe1 newLTe2)  

alphaConv (List l) context n = 
  let (newN, newL) = (alphaConvList l context n []) in
    (newN, List newL)

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

instantiate _ _ x = x


data EvalContext = EvalContext (Map String LTerm) Int Int deriving Show

data EvalFailureCause = EvaluationOver | EvaluationFailure String deriving Show

data EvalStepRes = 
  EvalStepSuccess LTerm EvalContext
  | EvalStepFailure LTerm EvalFailureCause deriving Show

getEvalStr :: String -> String -> String
getEvalStr oldterm newterm =
  "( " ++ oldterm ++ " -> " ++ newterm ++ " )"

{-
  given (App x y) and an EvalContext Ctx  
  this function takes as input x y Ctx and evaluates the application
  it's used by Eval_CBV_step
-}
evalApp :: LTerm -> LTerm -> EvalContext -> EvalStepRes
evalApp (Abs v body) arg evCtx =
  EvalStepSuccess (instantiate v arg body) evCtx

evalApp (App Hd (List (x:_))) _ evCtx =
  EvalStepSuccess x evCtx
evalApp (App Tl (List (_:xs))) _ evCtx =
  EvalStepSuccess (List xs) evCtx

evalApp (App Add (LInt arg1)) (LInt arg2) evCtx = 
  EvalStepSuccess (LInt (arg1 + arg2)) evCtx
evalApp (App Sub (LInt arg1)) (LInt arg2) evCtx = 
  EvalStepSuccess (LInt (arg1 - arg2)) evCtx

evalApp (App Cons arg1) (List arg2) evCtx = 
  EvalStepSuccess (List (arg1:arg2)) evCtx

evalApp (App Fix (Abs v body)) _ (EvalContext ctx n pn) =
  let (newN, newLTy) = alphaConv body (Map.fromList []) n in
    EvalStepSuccess (instantiate v newLTy body) (EvalContext ctx newN pn)

evalApp (App Ref lte) _ (EvalContext ctx n pn) =
  let newAddr = "p:" ++ show pn 
      newCtx = Map.insert newAddr lte ctx
  in 
    EvalStepSuccess (Vaddr newAddr) (EvalContext newCtx n  (pn + 1))

evalApp (App Deref (Vaddr newAddr)) _ (EvalContext ctx n pn) =
  case (Map.lookup newAddr ctx) of
    Just x -> EvalStepSuccess x (EvalContext ctx n pn)
    Nothing -> EvalStepFailure (App Deref (Var newAddr)) (EvaluationFailure "Deref failed: addr not in evaluation context")

evalApp (App Assign (Var x)) lte (EvalContext ctx n pn) =
  let newCtx = Map.insert x lte ctx in
    EvalStepSuccess (Unit) (EvalContext newCtx n pn)

evalApp f a _ = EvalStepFailure (App f a) (EvaluationFailure "evalApp : unevaluable")

{-
  Does one evaluation step
-}
eval_CBV_step :: LTerm -> EvalContext -> EvalStepRes  
eval_CBV_step (App lte1 lte2) (EvalContext ctx n pn) =
  case (eval_CBV_step lte1 (EvalContext ctx n pn)) of
    EvalStepSuccess newLTe1 (EvalContext newctx newN newpn) -> 
      EvalStepSuccess (App newLTe1 lte2) (EvalContext newctx newN newpn)
    EvalStepFailure _ _ ->(
      case (eval_CBV_step lte2 (EvalContext ctx n pn)) of
        EvalStepSuccess newLTe2 (EvalContext newctx newN newpn) ->
          EvalStepSuccess (App lte1 newLTe2) (EvalContext newctx newN newpn)
        EvalStepFailure _ _ -> 
          --EvalStepFailure (App lte1 lte2) ( (show lte1) ++ "  " ++ (show lte2) ))
          evalApp lte1 lte2 (EvalContext ctx n pn))

eval_CBV_step (Let x lte1 lte2) (EvalContext ctx n pn) =
  case (eval_CBV_step lte1 (EvalContext ctx n pn)) of
    EvalStepSuccess newLTe1 (EvalContext newctx newN newpn) ->
      EvalStepSuccess (Let x newLTe1 lte2) (EvalContext newctx newN newpn)
    EvalStepFailure _ _ -> 
      let newLTe2 = instantiate x lte1 lte2 in
        EvalStepSuccess newLTe2 (EvalContext ctx n pn)

eval_CBV_step (IfZ lte1 lte2 lte3) (EvalContext ctx n pn) =
  case (eval_CBV_step lte1 (EvalContext ctx n pn)) of
    EvalStepSuccess newLTe1 (EvalContext newctx newN newpn)-> 
      EvalStepSuccess (IfZ newLTe1 lte2 lte3) (EvalContext newctx newN newpn)
    EvalStepFailure _ _ ->
      case lte1 of 
        LInt x -> if x == 0 
          then (EvalStepSuccess lte2 (EvalContext ctx n pn)) 
          else (EvalStepSuccess lte3 (EvalContext ctx n pn))
        _ -> EvalStepFailure (IfZ lte1 lte2 lte3) (EvaluationFailure "Eval failure ifz") 

eval_CBV_step (IfE lte1 lte2 lte3) (EvalContext ctx n pn)=
  case (eval_CBV_step lte1 (EvalContext ctx n pn)) of
    EvalStepSuccess newLTe1 (EvalContext newctx newN newpn) ->
       EvalStepSuccess (IfZ newLTe1 lte2 lte3) (EvalContext newctx newN newpn)
    EvalStepFailure _ _ ->
      case lte1 of 
        LInt x -> if x == 0 
          then (EvalStepSuccess lte2 (EvalContext ctx n pn)) 
          else (EvalStepSuccess lte3 (EvalContext ctx n pn))
        _ -> EvalStepFailure (IfZ lte1 lte2 lte3) (EvaluationFailure "Eval failure ife")

eval_CBV_step lte _  = EvalStepFailure lte EvaluationOver


data EvalRes = 
  EvalSuccess [String] LTerm 
  | EvalFailure [String] LTerm String deriving Show

eval_CBV :: LTerm -> Int -> [String] -> EvalContext -> EvalRes
eval_CBV lte gas acc (EvalContext ctx n pn)
  | gas > 0 =
    case (eval_CBV_step lte (EvalContext ctx n pn)) of
      EvalStepSuccess newLTe (EvalContext newctx newN newpn)-> 
        eval_CBV newLTe (gas-1) (
          ("( gas = " ++ (show gas ) ++ ", " ++ 
          (show lte) ++ " -> " ++ (show newLTe) ++ " ) "):acc) (EvalContext newctx newN newpn)
      EvalStepFailure newLTe (EvaluationFailure msg) -> 
        EvalFailure (List.reverse acc) newLTe msg
      EvalStepFailure newLTe EvaluationOver -> EvalSuccess (List.reverse acc) newLTe
  | otherwise = EvalFailure (List.reverse acc) lte "eval_CBV failure: gas = 0"
