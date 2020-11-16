module Evaluation where

import Data.List as List
import Data.Map as Map
import Terms

data EvalContext = EvalContext (Map String LTerm) Int Int deriving (Show)

data EvalStopCause = EvalOver | EvalStepFailure String deriving (Show)

data EvalStepRes
  = EvalContinues LTerm EvalContext
  | EvalStops LTerm EvalStopCause
  deriving (Show)

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

lookupAndInsert :: String -> LTerm -> [(String, LTerm)] -> [(String, LTerm)]
lookupAndInsert str lte ((x, y) : tl)
  | str == x = (x, lte) : tl
  | otherwise = (x, y) : lookupAndInsert str lte tl
lookupAndInsert str _ [] = error ("lookupAndInsert  " ++ str ++ " not in Record!")

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
  | otherwise = EvalStops (App Hd x) (EvalStepFailure "[[[failcause : 1.1]]]")
evalApp Hd (List (x : _)) evCtx =
  EvalContinues x evCtx
evalApp Hd x evCtx
  | evaluable x =
    case evalCBVstep x evCtx of
      EvalContinues newlte newctx ->
        EvalContinues (App Hd newlte) newctx
      EvalStops newlte stpc ->
        EvalStops (App Hd newlte) stpc
  | otherwise = EvalStops (App Hd x) (EvalStepFailure "[[[failcause : 1.2]]]")
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
  | otherwise = EvalStops (App Tl x) (EvalStepFailure "[[[failcause : 2.1]]]")
evalApp Tl (List (_ : xs)) evCtx =
  EvalContinues (List xs) evCtx
evalApp Tl x evCtx
  | evaluable x =
    case evalCBVstep x evCtx of
      EvalContinues newlte newctx ->
        EvalContinues (App Tl newlte) newctx
      EvalStops newlte stpc ->
        EvalStops (App Tl newlte) stpc
  | otherwise = EvalStops (App Tl x) (EvalStepFailure "[[[failcause : 2.2]]")
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
  | otherwise = EvalStops (App (App Add (LInt arg1)) x) (EvalStepFailure "[[[failcause : 3.1]]]")
evalApp (App Add x) (LInt arg2) evCtx
  | evaluable x =
    case evalCBVstep x evCtx of
      EvalContinues newlte newctx ->
        EvalContinues (App (App Add newlte) (LInt arg2)) newctx
      EvalStops newlte stpc ->
        EvalStops (App (App Add newlte) (LInt arg2)) stpc
  | otherwise = EvalStops (App (App Add x) (LInt arg2)) (EvalStepFailure "[[[failcause : 3.2]]]")
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
  | otherwise = EvalStops (App (App Sub (LInt arg1)) x) (EvalStepFailure "[[[failcause : 4.1]]]")
evalApp (App Sub x) (LInt arg2) evCtx
  | evaluable x =
    case evalCBVstep x evCtx of
      EvalContinues newlte newctx ->
        EvalContinues (App (App Sub newlte) (LInt arg2)) newctx
      EvalStops newlte stpc ->
        EvalStops (App (App Sub newlte) (LInt arg2)) stpc
  | otherwise = EvalStops (App (App Sub x) (LInt arg2)) (EvalStepFailure "[[[failcause : 4.2]]]")
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
  | otherwise = EvalStops (App (App Cons (LInt arg1)) x) (EvalStepFailure "[[[failcause : 5.1]]]")
{-
evalApp (App Cons x) (LInt arg2) evCtx
  | evaluable x =
    case evalCBVstep x evCtx of
      EvalContinues newlte newctx ->
        EvalContinues (App (App Cons newlte) (LInt arg2)) newctx
      EvalStops newlte stpc ->
        EvalStops (App (App Cons newlte) (LInt arg2)) stpc
  | otherwise = EvalStops (App (App Cons x) (LInt arg2)) (EvalStepFailure "[[[failcause : 5.2]]]")
-}
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
  | otherwise = EvalStops (App (App Cons x) y) (EvalStepFailure "[[[failcause : 5.3]]]")
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
    Nothing -> EvalStops (App Deref (Var newAddr)) (EvalStepFailure "Deref failure: addr not in evaluation context")
evalApp Deref (Vaddr newAddr) (EvalContext ctx n pn) =
  case Map.lookup newAddr ctx of
    Just x -> EvalContinues x (EvalContext ctx n pn)
    Nothing -> EvalStops (App Deref (Var newAddr)) (EvalStepFailure "Deref failure: addr not in evaluation context")
evalApp (App Assign (Vaddr x)) lte (EvalContext ctx n pn) =
  let newCtx = Map.insert x lte ctx
   in EvalContinues Unit (EvalContext newCtx n pn)
--------------------------------------------------------------------------------------------------
evalApp (App (Get x) (Record l)) _ (EvalContext ctx n pn) =
  case List.lookup x l of
    Nothing -> EvalStops (App (Get x) (Record l)) (EvalStepFailure (show x ++ " not in " ++ show (Record l)))
    Just res -> EvalContinues res (EvalContext ctx n pn)
evalApp (Get x) (Record l) (EvalContext ctx n pn) =
  case List.lookup x l of
    Nothing -> EvalStops (App (Get x) (Record l)) (EvalStepFailure (show x ++ " not in " ++ show (Record l)))
    Just res -> EvalContinues res (EvalContext ctx n pn)
evalApp (App (Set x) (Record l)) lte (EvalContext ctx n pn) =
  case List.lookup x l of
    Nothing -> EvalStops (Record l) (EvalStepFailure (show x ++ " not in " ++ show (Record l)))
    Just _ -> EvalContinues (Record (lookupAndInsert x lte l)) (EvalContext ctx n pn)
--------------------------------------------------------------------------------------------------
evalApp f a _ = EvalStops (App f a) (EvalStepFailure ("evalApp : unevaluable ((( " ++ show (App f a) ++ " )))"))

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
        _ -> EvalStops (IfZ lte1 lte2 lte3) (EvalStepFailure "Eval failure ifz")
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
        _ -> EvalStops (IfZ lte1 lte2 lte3) (EvalStepFailure "Eval failure ife")
evalCBVstep lte _ = EvalStops lte EvalOver

evalCBVrec :: LTerm -> Int -> Int -> [String] -> EvalContext -> EvalRes
evalCBVrec lte nbsteps maxnbsteps acc (EvalContext ctx n pn)
  | maxnbsteps > nbsteps =
    case evalCBVstep lte (EvalContext ctx n pn) of
      EvalContinues newLTe (EvalContext newctx newN newpn) ->
        evalCBVrec
          newLTe
          (nbsteps + 1)
          maxnbsteps
          ((show nbsteps ++ " | " ++ show newLTe) : acc)
          (EvalContext newctx newN newpn)
      EvalStops newLTe (EvalStepFailure msg) ->
        EvalFailure (List.reverse acc) newLTe msg
      EvalStops newLTe EvalOver -> EvalSuccess (List.reverse acc) lte newLTe
  | otherwise = EvalFailure (List.reverse acc) lte "step limit atteined"

evalCBV :: LTerm -> Int -> EvalRes
evalCBV lte maxnbsteps = evalCBVrec lte 1 maxnbsteps ["0 | " ++ show lte] (makeEvalContext ())
