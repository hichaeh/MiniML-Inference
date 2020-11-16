module Terms where

import Data.Bifunctor
import Data.List as List
import Data.Map as Map

data LTerm
  = Var String
  | App LTerm LTerm
  | Abs String LTerm
  | IfZ LTerm LTerm LTerm -- ifZero
  | IfE LTerm LTerm LTerm -- ifEmpty
  | Let String LTerm LTerm
  | LInt Int
  | List [LTerm]
  | Unit
  | Add
  | Sub
  | Cons
  | Hd
  | Tl
  | Fix
  | Ref
  | Deref
  | Vaddr String -- Ref x -> Addr p.
  | Assign
  | Record [(String, LTerm)]
  | Get String
  | Set String
  deriving (Eq)

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
  show (Vaddr str) = "@" ++ str
  show (App (App Add x) y) = "( " ++ show x ++ show Add ++ show y ++ " )"
  show (App (App Sub x) y) = "( " ++ show x ++ show Sub ++ show y ++ " )"
  show (App (App Cons x) y) = "( " ++ show x ++ show Cons ++ show y ++ " )"
  show (App Deref x) = "!" ++ show x
  show (App (App Assign x) y) = "( " ++ show x ++ show Assign ++ show y ++ " )"
  show (App Add x) = "(+) " ++ show x
  show (App Sub x) = "(-) " ++ show x
  show (App Cons x) = "(cons) " ++ show x
  show Unit = "□"
  show (App (Get x) y) =
    show y ++ "[" ++ show x ++ "]"
  show (App (App (Set x) y) z) =
    show y ++ "[" ++ show x ++ "] <- " ++ show z
  show (App x y) = "(" ++ show x ++ " " ++ show y ++ ")"
  show (Record fl) = "{" ++ List.intercalate ", " (List.map (\(x, y) -> x ++ ":" ++ show y) fl) ++ "}"
  show _ = "[show : undexpected constructor]"

{-
  applies the alpha conversion on evety term in the first list
  2nd arg is the renaming context (keeps track of the new var names)
  3rd arg is the counter (allows us to give each var a different name)
  3th arg is he accumulation list were the terms are sotred after conversion
-}
alphaConvList :: [LTerm] -> Map String String -> Int -> [LTerm] -> (Int, [LTerm])
alphaConvList ((Var str) : tl) context n acc =
  case Map.lookup str context of
    Just x -> alphaConvList tl context n (Var x : acc)
    Nothing -> alphaConvList tl (Map.insert str ("x" ++ show n) context) (n + 1) (Var ("x" ++ show n) : acc)
alphaConvList (hd : tl) context n acc =
  let (newN, newLT) = alphaConv hd context n
   in alphaConvList tl context newN (newLT : acc)
alphaConvList [] _ n acc = (n, List.reverse acc)

{-
  applies the alpha conversion on every couple in the first list
  2nd arg is the renaming context (keeps track of the new var names)
  3rd arg is the counter (allows us to give each var a different name)
  3th arg is he accumulation list were the couples are sotred after conversion
-}
alphaConvCplList :: [(String, LTerm)] -> Map String String -> Int -> [(String, LTerm)] -> (Int, [(String, LTerm)])
alphaConvCplList ((fname, Var str) : tl) context n acc =
  case Map.lookup str context of
    Just x -> alphaConvCplList tl context n ((fname, Var x) : acc)
    Nothing -> alphaConvCplList tl (Map.insert str ("x" ++ show n) context) (n + 1) ((fname, Var ("x" ++ show n)) : acc)
alphaConvCplList ((fn, lte) : tl) context n acc =
  let (newN, newLT) = alphaConv lte context n
   in alphaConvCplList tl context newN ((fn, newLT) : acc)
alphaConvCplList [] _ n acc = (n, List.reverse acc)

{-
  renames bound variables in a term so that each one has it's own name
-}
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
alphaConv (Record l) context n =
  let (newN, newL) = alphaConvCplList l context n []
   in (newN, Record newL)
alphaConv x _ n = (n, x)

{-
  replaces varToRep with newLT in the term that is the third argument
-}
instantiate :: String -> LTerm -> LTerm -> LTerm
instantiate varToRep newLT (Var x)
  | x == varToRep = newLT
  | otherwise = Var x
instantiate varToRep newLT (App lt1 lt2) =
  App
    (instantiate varToRep newLT lt1)
    (instantiate varToRep newLT lt2)
instantiate varToRep newLT (Abs var body) =
  Abs
    var
    (instantiate varToRep newLT body)
instantiate varToRep newLT (IfZ lte1 lte2 lte3) =
  IfZ
    (instantiate varToRep newLT lte1)
    (instantiate varToRep newLT lte2)
    (instantiate varToRep newLT lte3)
instantiate varToRep newLT (IfE lte1 lte2 lte3) =
  IfE
    (instantiate varToRep newLT lte1)
    (instantiate varToRep newLT lte2)
    (instantiate varToRep newLT lte3)
instantiate varToRep newLT (Let v lte1 lte2) =
  Let
    v
    (instantiate varToRep newLT lte1)
    (instantiate varToRep newLT lte2)
instantiate varToRep newLT (List l) =
  List (List.map (instantiate varToRep newLT) l)
instantiate varToRep newLT (Record l) =
  Record (List.map (Data.Bifunctor.second (instantiate varToRep newLT)) l)
instantiate _ _ x = x
