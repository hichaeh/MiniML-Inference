module Terms where

import Data.List as List
import Data.Map as Map

data LTerm
  = Var String
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
  | Assign
  deriving (Eq)

cons :: LTerm -> [LTerm] -> [LTerm]
cons hd tl = hd : tl

instance Show LTerm where
  show (Var x) = x
  show (Abs x y) = "λ" ++ x ++ ".(" ++ show y ++ ")"
  show (LInt x) = show x
  show (List l) = "[" ++ List.intercalate ", " (List.map show l) ++ "]"
  show (Let x y z) = "let " ++ x ++ " = " ++ show y ++ " in " ++ show z
  show (IfZ x y z) = "ifZero " ++ show x ++ " then " ++ show y ++ " else " ++ show z
  show (IfE x y z) = "ifEmpty " ++ show x ++ " then " ++ show y ++ " else " ++ show z
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
  show (App (App Add x) y) = "( " ++ show x ++ show Add ++ show y ++ " )"
  show (App (App Sub x) y) = "( " ++ show x ++ show Sub ++ show y ++ " )"
  show (App (App Cons x) y) = "( " ++ show x ++ show Cons ++ show y ++ " )"
  show (App Deref x) = "!" ++ show x
  show (App (App Assign x) y) = "( " ++ show x ++ show Assign ++ show y ++ " )"
  show (App Add x) = "(+) " ++ show x
  show (App Sub x) = "(-) " ++ show x
  show (App Cons x) = "(cons) " ++ show x
  show Unit = "□"
  show (App x y) = "(" ++ show x ++ " " ++ show y ++ ")"

alphaConvList :: [LTerm] -> Map String String -> Int -> [LTerm] -> (Int, [LTerm])
alphaConvList ((Var str) : tl) context n acc =
  case Map.lookup str context of
    Just x -> alphaConvList tl context n (Var x : acc)
    Nothing -> alphaConvList tl (Map.insert str ("x" ++ show n) context) (n + 1) (Var ("x" ++ show n) : acc)
alphaConvList (hd : tl) context n acc =
  let (newN, newLT) = alphaConv hd context n
   in alphaConvList tl context newN (newLT : acc)
alphaConvList [] _ n acc = (n, List.reverse acc)

alphaConv :: LTerm -> Map String String -> Int -> (Int, LTerm)
alphaConv (Var v) context n =
  case Map.lookup v context of
    Just x -> (n, Var x)
    Nothing -> (n, Var v)
alphaConv (Abs var body) context n =
  let newContext = Map.insert var ("x" ++ show n) context
   in let (newN, newLTe) = alphaConv body newContext (n + 1)
       in (newN, Abs ("x" ++ show n) newLTe)
alphaConv (App lterm1 lterm2) context n =
  let (newN1, newLterm1) = alphaConv lterm1 context n
   in let (newN2, newLterm2) = alphaConv lterm2 context newN1
       in (newN2, App newLterm1 newLterm2)
alphaConv (IfZ lte1 lte2 lte3) context n =
  let (newN1, newLTe1) = alphaConv lte1 context n
   in let (newN2, newLTe2) = alphaConv lte2 context newN1
       in let (newN3, newLTe3) = alphaConv lte3 context newN2
           in (newN3, IfZ newLTe1 newLTe2 newLTe3)
alphaConv (IfE lte1 lte2 lte3) context n =
  let (newN1, newLTe1) = alphaConv lte1 context n
   in let (newN2, newLTe2) = alphaConv lte2 context newN1
       in let (newN3, newLTe3) = alphaConv lte3 context newN2
           in (newN3, IfE newLTe1 newLTe2 newLTe3)
alphaConv (Let str lte1 lte2) context n =
  let (newN1, newLTe1) = alphaConv lte1 newContext n
      newVStr = "x" ++ show newN1
      newContext = Map.insert str newVStr context
      (newN2, newLTe2) = alphaConv lte2 newContext (newN1 + 1)
   in (newN2, Let newVStr newLTe1 newLTe2)
alphaConv (List l) context n =
  let (newN, newL) = alphaConvList l context n []
   in (newN, List newL)
alphaConv x _ n = (n, x)

--
instantiate :: String -> LTerm -> LTerm -> LTerm
instantiate varToRep newLT (Var x)
  | x == varToRep = newLT
  | otherwise = Var x
instantiate varToRep newLT (App lt1 lt2) =
  App (instantiate varToRep newLT lt1) (instantiate varToRep newLT lt2)
instantiate varToRep newLT (Abs var body) =
  Abs var (instantiate varToRep newLT body)
instantiate varToRep newLT (IfZ lte1 lte2 lte3) =
  IfZ (instantiate varToRep newLT lte1) (instantiate varToRep newLT lte2) (instantiate varToRep newLT lte3)
instantiate varToRep newLT (IfE lte1 lte2 lte3) =
  IfE (instantiate varToRep newLT lte1) (instantiate varToRep newLT lte2) (instantiate varToRep newLT lte3)
instantiate varToRep newLT (Let v lte1 lte2) =
  Let v (instantiate varToRep newLT lte1) (instantiate varToRep newLT lte2)
instantiate varToRep newLT (List l) =
  List (List.map (instantiate varToRep newLT) l)
instantiate _ _ x = x

data EvalContext = EvalContext (Map String LTerm) Int Int deriving (Show)

data EvalStopCause = EvaluationOver | EvaluationFailure String deriving (Show)

data EvalStepRes
  = EvalContinues LTerm EvalContext
  | EvalStops LTerm EvalStopCause
  deriving (Show)

makeEvalContext :: () -> EvalContext
makeEvalContext () = EvalContext Map.empty 1 1

getEvalStr :: String -> String -> String
getEvalStr oldterm newterm =
  "( " ++ oldterm ++ " -> " ++ newterm ++ " )"

{-
  given (App x y) and an EvalContext Ctx
  this function takes as input x y Ctx and evaluates the application
  it's used by evalCBVstep
-}
evaluable :: LTerm -> Bool
evaluable App {} = True
evaluable IfE {} = True
evaluable IfZ {} = True
evaluable _ = False

evalApp :: LTerm -> LTerm -> EvalContext -> EvalStepRes
evalApp (Abs v body) arg evCtx =
  EvalContinues (instantiate v arg body) evCtx
--------------------------------------------------------------------------------------------------
evalApp (App Hd (List (x : _))) _ evCtx =
  EvalContinues x evCtx
evalApp (App Hd x) _ evCtx
  | evaluable x =
    case evalCBVstep x evCtx of
      EvalContinues newlte newctx ->
        EvalContinues (App Hd newlte) newctx
      EvalStops newlte stpc ->
        EvalStops (App Hd newlte) stpc
  | otherwise = EvalStops (App Hd x) (EvaluationFailure "[[[failcause1]]]")
evalApp Hd (List (x : _)) evCtx =
  EvalContinues x evCtx
evalApp Hd x evCtx
  | evaluable x =
    case evalCBVstep x evCtx of
      EvalContinues newlte newctx ->
        EvalContinues (App Hd newlte) newctx
      EvalStops newlte stpc ->
        EvalStops (App Hd newlte) stpc
  | otherwise = EvalStops (App Hd x) (EvaluationFailure "[[[failcause1]]]")
--------------------------------------------------------------------------------------------------
evalApp (App Tl (List (_ : xs))) _ evCtx =
  EvalContinues (List xs) evCtx
evalApp (App Tl x) _ evCtx
  | evaluable x =
    case evalCBVstep x evCtx of
      EvalContinues newlte newctx ->
        EvalContinues (App Tl newlte) newctx
      EvalStops newlte stpc ->
        EvalStops (App Tl newlte) stpc
  | otherwise = EvalStops (App Tl x) (EvaluationFailure "[[[failcause2]]]")
evalApp Tl (List (_ : xs)) evCtx =
  EvalContinues (List xs) evCtx
evalApp Tl x evCtx
  | evaluable x =
    case evalCBVstep x evCtx of
      EvalContinues newlte newctx ->
        EvalContinues (App Tl newlte) newctx
      EvalStops newlte stpc ->
        EvalStops (App Tl newlte) stpc
  | otherwise = EvalStops (App Tl x) (EvaluationFailure "[[[failcause2]]]")
--------------------------------------------------------------------------------------------------
evalApp (App Add (LInt arg1)) (LInt arg2) evCtx =
  EvalContinues (LInt (arg1 + arg2)) evCtx
evalApp (App Add (LInt arg1)) x evCtx
  | evaluable x =
    case evalCBVstep x evCtx of
      EvalContinues newlte newctx ->
        EvalContinues (App (App Add (LInt arg1)) newlte) newctx
      EvalStops newlte stpc ->
        EvalStops (App (App Add (LInt arg1)) newlte) stpc
  | otherwise = EvalStops (App (App Add (LInt arg1)) x) (EvaluationFailure "[[[failcause:3.1]]]")
evalApp (App Add x) (LInt arg2) evCtx
  | evaluable x =
    case evalCBVstep x evCtx of
      EvalContinues newlte newctx ->
        EvalContinues (App (App Add newlte) (LInt arg2)) newctx
      EvalStops newlte stpc ->
        EvalStops (App (App Add newlte) (LInt arg2)) stpc
  | otherwise = EvalStops (App (App Add x) (LInt arg2)) (EvaluationFailure "[[[failcause:3.2]]]")
--------------------------------------------------------------------------------------------------
evalApp (App Sub (LInt arg1)) (LInt arg2) evCtx =
  EvalContinues (LInt (arg1 - arg2)) evCtx
evalApp (App Sub (LInt arg1)) x evCtx
  | evaluable x =
    case evalCBVstep x evCtx of
      EvalContinues newlte newctx ->
        EvalContinues (App (App Sub (LInt arg1)) newlte) newctx
      EvalStops newlte stpc ->
        EvalStops (App (App Sub (LInt arg1)) newlte) stpc
  | otherwise = EvalStops (App (App Sub (LInt arg1)) x) (EvaluationFailure "[[[failcause:4.1]]]")
evalApp (App Sub x) (LInt arg2) evCtx
  | evaluable x =
    case evalCBVstep x evCtx of
      EvalContinues newlte newctx ->
        EvalContinues (App (App Sub newlte) (LInt arg2)) newctx
      EvalStops newlte stpc ->
        EvalStops (App (App Sub newlte) (LInt arg2)) stpc
  | otherwise = EvalStops (App (App Sub x) (LInt arg2)) (EvaluationFailure "[[[failcause:4.2]]]")
--------------------------------------------------------------------------------------------------
evalApp (App Cons arg1) (List arg2) evCtx =
  EvalContinues (List (arg1 : arg2)) evCtx
evalApp (App Cons (LInt arg1)) x evCtx
  | evaluable x =
    case evalCBVstep x evCtx of
      EvalContinues newlte newctx ->
        EvalContinues (App (App Cons (LInt arg1)) newlte) newctx
      EvalStops newlte stpc ->
        EvalStops (App (App Cons (LInt arg1)) newlte) stpc
  | otherwise = EvalStops (App (App Cons (LInt arg1)) x) (EvaluationFailure "[[[failcause:5.1]]]")
evalApp (App Cons x) (LInt arg2) evCtx
  | evaluable x =
    case evalCBVstep x evCtx of
      EvalContinues newlte newctx ->
        EvalContinues (App (App Cons newlte) (LInt arg2)) newctx
      EvalStops newlte stpc ->
        EvalStops (App (App Cons newlte) (LInt arg2)) stpc
  | otherwise = EvalStops (App (App Cons x) (LInt arg2)) (EvaluationFailure "[[[failcause:5.2]]]")
evalApp (App Cons x) y evCtx
  | evaluable x && evaluable y =
    case evalCBVstep x evCtx of
      EvalStops newlte stpc ->
        EvalStops (App (App Cons newlte) y) stpc
      EvalContinues newlte1 newctx1 ->
        case evalCBVstep y newctx1 of
          EvalContinues newlte2 newctx2 ->
            EvalContinues (App (App Cons newlte1) newlte2) newctx2
          EvalStops newlte stpc ->
            EvalStops (App (App Cons newlte1) newlte) stpc
  | evaluable x =
    case evalCBVstep x evCtx of
      EvalStops newlte stpc ->
        EvalStops (App (App Cons newlte) y) stpc
      EvalContinues newlte1 newctx1 ->
        EvalContinues (App (App Cons newlte1) y) newctx1
  | evaluable y =
    case evalCBVstep y evCtx of
      EvalStops newlte stpc ->
        EvalStops (App (App Cons newlte) y) stpc
      EvalContinues newlte1 newctx1 ->
        EvalContinues (App (App Cons x) newlte1) newctx1
  | otherwise = EvalStops (App (App Cons x) y) (EvaluationFailure "[[[failcause:5.3]]]")
--------------------------------------------------------------------------------------------------
evalApp (App Fix (Abs v body)) arg (EvalContext ctx n pn) =
  let (newN, newLTy) = alphaConv body Map.empty n
   in EvalContinues (App (instantiate v (App Fix (Abs v body)) newLTy) arg) (EvalContext ctx newN pn)
evalApp (App Ref lte) _ (EvalContext ctx n pn) =
  let newAddr = "p:" ++ show pn
      newCtx = Map.insert newAddr lte ctx
   in EvalContinues (Vaddr newAddr) (EvalContext newCtx n (pn + 1))
evalApp Ref lte (EvalContext ctx n pn) =
  let newAddr = "p:" ++ show pn
      newCtx = Map.insert newAddr lte ctx
   in EvalContinues (Vaddr newAddr) (EvalContext newCtx n (pn + 1))
evalApp (App Deref (Vaddr newAddr)) _ (EvalContext ctx n pn) =
  case Map.lookup newAddr ctx of
    Just x -> EvalContinues x (EvalContext ctx n pn)
    Nothing -> EvalStops (App Deref (Var newAddr)) (EvaluationFailure "Deref failed: addr not in evaluation context")
evalApp Deref (Vaddr newAddr) (EvalContext ctx n pn) =
  case Map.lookup newAddr ctx of
    Just x -> EvalContinues x (EvalContext ctx n pn)
    Nothing -> EvalStops (App Deref (Var newAddr)) (EvaluationFailure "Deref failed: addr not in evaluation context")
evalApp (App Assign (Vaddr x)) lte (EvalContext ctx n pn) =
  let newCtx = Map.insert x lte ctx
   in EvalContinues Unit (EvalContext newCtx n pn)
--------------------------------------------------------------------------------------------------
{-
evalApp (App bop x) y evCtx
  | evaluable x && evaluable y =
    case List.elem bop (Add : Sub : Cons : [])) of
      False -> EvalStops (App (App bop x) y) (EvaluationFailure "[[[failcause:6]]]")
      True ->
        case evalCBVstep x evCtx of
          EvalStops newlte stpc ->
            EvalStops (App (App bop newlte) y) stpc
          EvalContinues newlte1 newctx1 ->
            case evalCBVstep y newctx1) of
              EvalContinues newlte2 newctx2 ->
                EvalContinues (App (App bop newlte1) newlte2) newctx2
              EvalStops newlte stpc ->
                EvalStops (App (App bop newlte1) newlte) stpc
  | evaluable x =
    case List.elem bop (Add : Sub : Cons : [])) of
      False -> EvalStops (App (App bop x) y) (EvaluationFailure "[[[failcause:6]]]")
      True ->
        case evalCBVstep x evCtx of
          EvalStops newlte stpc ->
            EvalStops (App (App bop newlte) y) stpc
          EvalContinues newlte1 newctx1 ->
            EvalContinues (App (App bop newlte1) y) newctx1
  | evaluable y =
    case List.elem bop (Add : Sub : Cons : [])) of
      False -> EvalStops (App (App bop x) y) (EvaluationFailure "[[[failcause:6]]]")
      True ->
        case evalCBVstep y evCtx of
          EvalStops newlte stpc ->
            EvalStops (App (App Cons newlte) y) stpc
          EvalContinues newlte1 newctx1 ->
            EvalContinues (App (App Cons x) newlte1) newctx1
  | otherwise = EvalStops (App (App Cons x) y) (EvaluationFailure "[[[failcause:6]]]")
--------------------------------------------------------------------------------------------------
evalApp uop x evCtx
  | evaluable x =
    case List.elem uop (Hd : Tl : [])) of
      False -> EvalStops (App uop x) (EvaluationFailure "[[[failcause:7]]]")
      True ->
        case evalCBVstep x evCtx of
          EvalContinues newlte newctx ->
            EvalContinues (App uop newlte) newctx
          EvalStops newlte stpc ->
            EvalStops (App uop newlte) stpc
  | otherwise = EvalStops (App uop x) (EvaluationFailure "[[[failcause:7]]]")
--------------------------------------------------------------------------------------------------
-}
evalApp f a _ = EvalStops (App f a) (EvaluationFailure ("evalApp : unevaluable (((" ++ show (App f a) ++ ")" ++ show f ++ "    " ++ show a ++ "))"))

{-
  Does one evaluation step
-}
evalCBVstep :: LTerm -> EvalContext -> EvalStepRes
evalCBVstep (App lte1 lte2) (EvalContext ctx n pn) =
  case evalCBVstep lte1 (EvalContext ctx n pn) of
    EvalContinues newLTe1 (EvalContext newctx newN newpn) ->
      EvalContinues (App newLTe1 lte2) (EvalContext newctx newN newpn)
    EvalStops _ _ ->
      case evalCBVstep lte2 (EvalContext ctx n pn) of
        EvalContinues newLTe2 (EvalContext newctx newN newpn) ->
          EvalContinues (App lte1 newLTe2) (EvalContext newctx newN newpn)
        EvalStops _ _ ->
          evalApp lte1 lte2 (EvalContext ctx n pn)
evalCBVstep (Let x lte1 lte2) (EvalContext ctx n pn) =
  case evalCBVstep lte1 (EvalContext ctx n pn) of
    EvalContinues newLTe1 (EvalContext newctx newN newpn) ->
      EvalContinues (Let x newLTe1 lte2) (EvalContext newctx newN newpn)
    EvalStops _ _ ->
      let newLTe2 = instantiate x lte1 lte2
       in EvalContinues newLTe2 (EvalContext ctx n pn)
evalCBVstep (IfZ lte1 lte2 lte3) (EvalContext ctx n pn) =
  case evalCBVstep lte1 (EvalContext ctx n pn) of
    EvalContinues newLTe1 (EvalContext newctx newN newpn) ->
      EvalContinues (IfZ newLTe1 lte2 lte3) (EvalContext newctx newN newpn)
    EvalStops _ _ ->
      case lte1 of
        LInt x ->
          if x == 0
            then EvalContinues lte2 (EvalContext ctx n pn)
            else EvalContinues lte3 (EvalContext ctx n pn)
        _ -> EvalStops (IfZ lte1 lte2 lte3) (EvaluationFailure "Eval failure ifz")
evalCBVstep (IfE lte1 lte2 lte3) (EvalContext ctx n pn) =
  case evalCBVstep lte1 (EvalContext ctx n pn) of
    EvalContinues newLTe1 (EvalContext newctx newN newpn) ->
      EvalContinues (IfZ newLTe1 lte2 lte3) (EvalContext newctx newN newpn)
    EvalStops _ _ ->
      case lte1 of
        List x ->
          if List.null x
            then EvalContinues lte2 (EvalContext ctx n pn)
            else EvalContinues lte3 (EvalContext ctx n pn)
        _ -> EvalStops (IfZ lte1 lte2 lte3) (EvaluationFailure "Eval failure ife")
evalCBVstep lte _ = EvalStops lte EvaluationOver

data EvalRes
  = EvalSuccess [String] LTerm LTerm
  | EvalFailure [String] LTerm String

instance Show EvalRes where
  show (EvalSuccess strl lte newlte) =
    "Evaluation) of  : " ++ show lte ++ "\n\n"
      ++ List.intercalate "\n" strl
      ++ "\n\n"
      ++ "The evaluation succeeded! result : "
      ++ show newlte
      ++ "\n\n"
  show (EvalFailure strl lte msg) =
    "Evaluation) of  : " ++ show lte ++ "\n\n"
      ++ List.intercalate "\n" strl
      ++ "\n\n"
      ++ "The evaluation failed! cause : "
      ++ msg
      ++ "\n\n"

evalCBVrec :: LTerm -> Int -> Int -> [String] -> EvalContext -> EvalRes
evalCBVrec lte nbsteps maxnbsteps acc (EvalContext ctx n pn)
  | maxnbsteps > nbsteps =
    case evalCBVstep lte (EvalContext ctx n pn) of
      EvalContinues newLTe (EvalContext newctx newN newpn) ->
        evalCBVrec
          newLTe
          (nbsteps + 1)
          maxnbsteps
          ( ( show nbsteps ++ " | "
                ++ show newLTe
            ) :
            acc
          )
          (EvalContext newctx newN newpn)
      EvalStops newLTe (EvaluationFailure msg) ->
        EvalFailure (List.reverse acc) newLTe msg
      EvalStops newLTe EvaluationOver -> EvalSuccess (List.reverse acc) lte newLTe
  | otherwise = EvalFailure (List.reverse acc) lte "step limit atteined"

evalCBV :: LTerm -> Int -> EvalRes
evalCBV lte maxnbsteps = evalCBVrec lte 1 maxnbsteps ["0 | " ++ show lte] (makeEvalContext ())

--debug
getResLTfromEvalRes :: EvalRes -> LTerm
getResLTfromEvalRes (EvalSuccess _ _ lte) = lte
getResLTfromEvalRes (EvalFailure _ _ msg) = error ("Can't Get evaluation result, it failed! " ++ msg)

--debug
evalsteprescontinue :: EvalStepRes -> EvalStepRes
evalsteprescontinue (EvalContinues lte (EvalContext ctx n pn)) =
  evalCBVstep lte (EvalContext ctx n pn)
evalsteprescontinue x = x

{-
data EvalContext = EvalContext (Map String LTerm) Int Int deriving (Show)
data EvalStopCause = EvaluationOver | EvaluationFailure String deriving (Show)
data EvalStepRes
  = EvalContinues LTerm EvalContext
  | EvalStops LTerm EvalStopCause
  deriving (Show)

-}

--App (App (App Fix (Abs "map" ( Abs "f" (Abs "l" ( IfE (Var "l") (List [])
-- (App (App Cons x1) x2)))))) (App Add (LInt 5) )) (List ((LInt 1):(LInt 2):(LInt 3):[]))
--App (App (App Fix (Abs "map" ( Abs "f" (Abs "l" ( IfE (Var "l") (List []) (App (App Cons x1) x2)))))) (App Add (LInt 5) )) (List ((LInt 1):(LInt 2):(LInt 3):[]))

{-
(
  (
    (
      (
        ( 5 + (hd [1, 2, 3]) )
        ::
        ifEmpty (tl [1, 2, 3])
          then []
          else
            (
              ( 5 + (hd (tl [1, 2, 3])) )
              ::
              (
                (
                  (
                    fix λmap.(λf.(λl.(
                      ifEmpty l
                      then []
                      else
                        ( (f (hd l))
                        ::((map f) (tl l)) )
                    )))
                  ) 5
                ) (tl (tl [1, 2, 3]))
              )
            )
      )
    )
  )
)

let x1 = App  (Var "f") (App Hd (Var "l") )
let x21 = App (Var "map") (Var "f")
let x22 = App Tl (Var "l")
let x2 = App x21 x22
let a = App Fix (Abs "map" ( Abs "f" (Abs "l" ( IfE (Var "l") (List []) (App (App Cons x1) x2)  ))))

-}