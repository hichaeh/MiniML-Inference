module TypeInference where

import Data.List as List
import Data.Map as Map
import Terms
import Types

occurCheck :: LType -> LType -> Bool
occurCheck (TVar x) (TVar y) =
  x == y
occurCheck tyv (TArrow lty1 lty2) =
  tyv == TArrow lty1 lty2 || occurCheck tyv lty1 || occurCheck tyv lty2
occurCheck tyv (TList ltype) =
  tyv == TList ltype || occurCheck tyv ltype
occurCheck tyv (TPoly x ltype) =
  tyv == TPoly x ltype || occurCheck tyv ltype
occurCheck tyv (TRef x) =
  tyv == TRef x || occurCheck tyv x
occurCheck tyv (WVT str lty) =
  tyv == WVT str lty || occurCheck tyv lty
occurCheck tyv (WVF str) =
  tyv == WVF str || TVar str == tyv
occurCheck tyv (WF b x lty) =
  tyv == WF b x lty || occurCheck tyv lty
occurCheck _ _ = False

alphaConvTypes :: LType -> Map String String -> Int -> (Int, LType)
alphaConvTypes (TVar x) ctx n =
  case Map.lookup x ctx of
    Just y -> (n, TVar y)
    Nothing -> (n, TVar x)
alphaConvTypes (WVT str lty) ctx n =
  let (newn, newlty) = alphaConvTypes lty ctx n
   in (newn, WVT str newlty)
alphaConvTypes (WVF str) ctx n =
  case Map.lookup str ctx of
    Just y -> (n, WVF y)
    Nothing -> (n, WVF str)
alphaConvTypes (TArrow x y) ctx n =
  let (newn1, newlty1) = alphaConvTypes x ctx n
      (newn2, newlty2) = alphaConvTypes y ctx newn1
   in (newn2, TArrow newlty1 newlty2)
alphaConvTypes (TList lty) ctx n =
  let (newn, newlty) = alphaConvTypes lty ctx n
   in (newn, TList newlty)
alphaConvTypes (TRef lty) ctx n =
  let (newn, newlty) = alphaConvTypes lty ctx n
   in (newn, TRef newlty)
alphaConvTypes (TPoly str lty) ctx n =
  let newT = "T" ++ show n
      (newn, newlty) = alphaConvTypes lty (Map.insert str newT ctx) (n + 1)
   in (newn, TPoly newT newlty)
alphaConvTypes (WF b x lty) ctx n
  | b =
    let (newn, newlty) = alphaConvTypes lty ctx n
     in (newn, WF True x newlty)
  | otherwise =
    let newT = "_T" ++ show n
        (newn, newlty) = alphaConvTypes lty (Map.insert x newT ctx) (n + 1)
     in (newn, WF False x newlty)
alphaConvTypes x _ n = (n, x)

mkString :: LTerm -> LType -> Int -> Map String LType -> String -> String
mkString lte lty n ctx str =
  "genEquas(lte= " ++ show lte ++ ",lty= " ++ show lty ++ ", n= " ++ show n ++ ",context= " ++ show ctx ++ ")\n -----> [ " ++ str ++ " ]\n\n"

data GenEquasContext = GenEquasContext Int (Map String LType)

data GenEquasRes
  = GenEquasSuccess Int [LTypeEqua] [String]
  | GenEquasFailed String [String]

getGRReqs :: GenEquasRes -> [LTypeEqua]
getGRReqs (GenEquasSuccess _ eqs _) = eqs
getGRReqs _ = error "errroooooooooor"

instance Show GenEquasRes where
  show (GenEquasSuccess n eqs strl) =
    "GenEquasSuccess : \n"
      ++ "    Eqs : \n"
      ++ show eqs
      ++ "\n n : \n"
      ++ show n
      ++ "     strl : \n"
      ++ List.intercalate "" strl
  show (GenEquasFailed str strl) =
    "GenEquasFailed : \n"
      ++ "    cause : "
      ++ str
      ++ "\n     strl : \n"
      ++ List.intercalate "\n" strl
      ++ "\n"

termListToEquaList :: [LTerm] -> LType -> GenEquasContext -> [String] -> GenEquasRes
termListToEquaList (x : xs) lty (GenEquasContext n ctx) trace =
  case genEquas x lty (GenEquasContext n ctx) trace of --(mget x lty n ctx trace) of
    GenEquasFailed msg trace1 -> GenEquasFailed msg trace1
    GenEquasSuccess newN1 lteqs1 trace1 ->
      case termListToEquaList xs lty (GenEquasContext newN1 ctx) trace1 of --(mgetl xs lty newN1 ctx trace) of
        GenEquasFailed msg trace2 -> GenEquasFailed msg trace2
        GenEquasSuccess newN2 lteqs2 trace2 ->
          GenEquasSuccess newN2 (lteqs1 ++ lteqs2) trace2
termListToEquaList [] _ (GenEquasContext n _) trace = GenEquasSuccess n [] trace

genEquas :: LTerm -> LType -> GenEquasContext -> [String] -> GenEquasRes
genEquas (Var x) lty (GenEquasContext n ctx) trace =
  case Map.lookup x ctx of
    Just ltyv ->
      GenEquasSuccess n [LTypeEqua lty ltyv] (mkString (Var x) lty n ctx (show (LTypeEqua lty ltyv)) : trace)
    Nothing ->
      GenEquasFailed " genEquasFailure Var unknown " (mkString (Var x) lty n ctx " genEquasFailure Var unknown " : trace)
genEquas (Abs v bodyLTe) lty (GenEquasContext n ctx) trace =
  let ltya = TVar ("T" ++ show n)
   in let ltyr = TVar ("T" ++ show (n + 1))
       in let newCtx = Map.insert v ltya ctx
           in case genEquas bodyLTe ltyr (GenEquasContext (n + 2) newCtx) trace of
                GenEquasSuccess newN newLTyEqs trace1 ->
                  GenEquasSuccess newN (LTypeEqua lty (TArrow ltya ltyr) : newLTyEqs) (mkString (Abs v bodyLTe) lty n ctx (show (LTypeEqua lty (TArrow ltya ltyr))) : trace1)
                GenEquasFailed msg trace1 -> GenEquasFailed msg trace1
genEquas (App Fix (Abs v body)) lty (GenEquasContext n ctx) trace =
  let tfix = TVar ("T" ++ show n)
   in case genEquas body tfix (GenEquasContext (n + 1) (Map.insert v tfix ctx)) trace of
        GenEquasSuccess newN newEqs trace1 -> GenEquasSuccess newN (LTypeEqua lty tfix : newEqs) (mkString (App Fix (Abs v body)) lty n ctx (show (LTypeEqua lty tfix)) : trace1)
        GenEquasFailed msg trace1 -> GenEquasFailed msg trace1
genEquas (LInt x) lty (GenEquasContext n ctx) trace =
  GenEquasSuccess n [LTypeEqua lty TInt] (mkString (LInt x) lty n ctx (show (LTypeEqua lty TInt)) : trace)
genEquas (List l) lty (GenEquasContext n ctx) trace =
  let newTV = TVar ("T" ++ show n)
      newEqua = LTypeEqua lty (TList newTV)
   in case termListToEquaList l newTV (GenEquasContext (n + 1) ctx) trace of
        GenEquasFailed msg trace1 -> GenEquasFailed msg trace1
        GenEquasSuccess newN lteqs trace1 ->
          GenEquasSuccess newN (newEqua : lteqs) (mkString (List l) lty n ctx (show newEqua) : trace1)
genEquas (IfZ lte1 lte2 lte3) lty (GenEquasContext n ctx) trace =
  let newT = TVar ("T" ++ show n)
   in case genEquas lte1 TInt (GenEquasContext (n + 1) ctx) trace of
        GenEquasFailed msg trace1 -> GenEquasFailed msg trace1
        GenEquasSuccess newN1 newEqs1 trace1 ->
          case genEquas lte2 newT (GenEquasContext newN1 ctx) trace1 of
            GenEquasFailed msg trace2 -> GenEquasFailed msg trace2
            GenEquasSuccess newN2 newEqs2 trace2 ->
              case genEquas lte3 newT (GenEquasContext newN2 ctx) trace2 of
                GenEquasFailed msg trace3 -> GenEquasFailed msg trace3
                GenEquasSuccess newN3 newEqs3 trace3 ->
                  GenEquasSuccess
                    newN3
                    (LTypeEqua lty newT : (newEqs1 ++ newEqs2 ++ newEqs3))
                    (mkString (IfZ lte1 lte2 lte3) lty n ctx (show (LTypeEqua lty newT : (newEqs1 ++ newEqs2 ++ newEqs3))) : trace3) --(aett (LTypeEqua lty newT) trace3)
genEquas (IfE lte1 lte2 lte3) lty (GenEquasContext n ctx) trace =
  let newTa = TVar ("T" ++ show n)
      newTn = TVar ("T" ++ show (n + 1))
   in case genEquas lte1 (TList newTa) (GenEquasContext (n + 2) ctx) trace of
        GenEquasFailed msg trace1 -> GenEquasFailed msg trace1
        GenEquasSuccess newN1 newEqs1 trace1 ->
          case genEquas lte2 newTn (GenEquasContext newN1 ctx) trace1 of
            GenEquasFailed msg trace2 -> GenEquasFailed msg trace2
            GenEquasSuccess newN2 newEqs2 trace2 ->
              case genEquas lte3 newTn (GenEquasContext newN2 ctx) trace2 of
                GenEquasFailed msg trace3 -> GenEquasFailed msg trace3
                GenEquasSuccess newN3 newEqs3 trace3 ->
                  GenEquasSuccess
                    newN3
                    (LTypeEqua lty newTn : (newEqs1 ++ newEqs2 ++ newEqs3))
                    (mkString (IfE lte1 lte2 lte3) lty n ctx (show (LTypeEqua lty newTn : (newEqs1 ++ newEqs2 ++ newEqs3))) : trace3)
genEquas (Let v lte1 lte2) lty (GenEquasContext n ctx) trace =
  case typeInferenceRec lte1 ctx of
    TypeInferenceSuccess _ newlte newLTy newtrace ->
      if isNonExpansible lte1
        then
          let newCtx = Map.insert v (generalise ctx newLTy) ctx
           in genEquas lte2 lty (GenEquasContext n newCtx) (trace ++ newtrace ++ ["\n type[" ++ show newlte ++ "] = " ++ show newLTy ++ " \n"])
        else
          let newCtx = Map.insert v (weakGeneralise newLTy) ctx
           in genEquas lte2 lty (GenEquasContext n newCtx) (trace ++ newtrace ++ ["\n type[" ++ show newlte ++ "] = " ++ show newLTy ++ " \n"])
    TypeInferenceFailure _ _ _ newtrace ->
      GenEquasFailed (" genEquasFailure {1} typeDetection of " ++ show lte1 ++ " in " ++ show ctx) (mkString Unit lty n ctx (" genEquasFailure {1} typeDetection of " ++ show lte1 ++ " in " ++ show ctx) : trace ++ newtrace)
genEquas Add lty (GenEquasContext n ctx) trace =
  GenEquasSuccess n [LTypeEqua lty (TArrow TInt (TArrow TInt TInt))] (mkString Add lty n ctx (show (LTypeEqua lty (TArrow TInt (TArrow TInt TInt)))) : trace)
genEquas Sub lty (GenEquasContext n ctx) trace =
  GenEquasSuccess n [LTypeEqua lty (TArrow TInt (TArrow TInt TInt))] (mkString Sub lty n ctx (show (LTypeEqua lty (TArrow TInt (TArrow TInt TInt)))) : trace)
genEquas Cons lty (GenEquasContext n ctx) trace =
  let newV = "T" ++ show n
      newT = TVar newV
   in GenEquasSuccess
        (n + 1)
        [LTypeEqua (TPoly newV (TArrow newT (TArrow (TList newT) (TList newT)))) lty]
        (mkString Cons lty n ctx (show (LTypeEqua (TPoly newV (TArrow newT (TArrow (TList newT) (TList newT)))) lty)) : trace)
genEquas Hd lty (GenEquasContext n ctx) trace =
  let newV = "T" ++ show n
      newT = TVar newV
   in GenEquasSuccess
        (n + 1)
        [LTypeEqua (TPoly newV (TArrow (TList newT) newT)) lty]
        (mkString Hd lty n ctx (show (LTypeEqua (TPoly newV (TArrow (TList newT) newT)) lty)) : trace)
genEquas Tl lty (GenEquasContext n ctx) trace =
  let newV = "T" ++ show n
      newT = TVar newV
   in GenEquasSuccess
        (n + 1)
        [LTypeEqua (TPoly newV (TArrow (TList newT) (TList newT))) lty]
        (mkString Tl lty n ctx (show (LTypeEqua (TPoly newV (TArrow (TList newT) newT)) lty)) : trace)
genEquas Ref lty (GenEquasContext n ctx) trace =
  let newV = "T" ++ show n
      newT = TPoly newV (TArrow (TVar newV) (TRef (TVar newV)))
   in GenEquasSuccess (n + 1) [LTypeEqua lty newT] (mkString Ref lty n ctx (show (LTypeEqua lty newT)) : trace)
genEquas Deref lty (GenEquasContext n ctx) trace =
  let newV = "T" ++ show n
      newT = TPoly newV (TArrow (TRef (TVar newV)) (TVar newV))
   in GenEquasSuccess (n + 1) [LTypeEqua lty newT] (mkString Deref lty n ctx (show (LTypeEqua lty newT)) : trace)
{-
genEquas (App (App Assign (Var x)) lte) lty (GenEquasContext n ctx) trace =
  case Map.lookup x ctx of
    Nothing ->
      let ltya = TVar ("T" ++ show n)
       in case genEquas (App Assign (Var x)) (TArrow ltya lty) (GenEquasContext (n + 1) ctx) trace of
            GenEquasFailed msg trace1 -> GenEquasFailed msg trace1
            GenEquasSuccess newN1 newLTyEquas1 trace1 ->
              case genEquas lte2 ltya (GenEquasContext newN1 ctx) trace1 of
                GenEquasFailed msg trace2 ->
                  GenEquasFailed msg trace2
                GenEquasSuccess newN2 newLTyEquas2 trace2 ->
                  GenEquasSuccess newN2 (newLTyEquas1 ++ newLTyEquas2) (mkString (App lte1 lte2) lty n ctx (show (newLTyEquas1 ++ newLTyEquas2)) : trace2)
    Just x -> undefined
-}

genEquas Assign lty (GenEquasContext n ctx) trace =
  let newV = "T" ++ show n
      newT = TPoly newV (TArrow (TRef (TVar newV)) (TArrow (TVar newV) TUnit))
   in GenEquasSuccess (n + 1) [LTypeEqua lty newT] (mkString Assign lty n ctx (show (LTypeEqua lty newT)) : trace)
genEquas (App lte1 lte2) lty (GenEquasContext n ctx) trace =
  let ltya = TVar ("T" ++ show n)
   in case genEquas lte1 (TArrow ltya lty) (GenEquasContext (n + 1) ctx) trace of
        GenEquasFailed msg trace1 -> GenEquasFailed msg trace1
        GenEquasSuccess newN1 newLTyEquas1 trace1 ->
          case genEquas lte2 ltya (GenEquasContext newN1 ctx) trace1 of
            GenEquasFailed msg trace2 ->
              GenEquasFailed msg trace2
            GenEquasSuccess newN2 newLTyEquas2 trace2 ->
              GenEquasSuccess newN2 (newLTyEquas1 ++ newLTyEquas2) (mkString (App lte1 lte2) lty n ctx (show (newLTyEquas1 ++ newLTyEquas2)) : trace2)
genEquas Unit lty (GenEquasContext n ctx) trace =
  GenEquasSuccess n [LTypeEqua lty TUnit] (mkString Unit lty n ctx (show (LTypeEqua lty TUnit)) : trace)
genEquas _ lty (GenEquasContext n ctx) trace =
  GenEquasFailed " genEquasFailure {} " (mkString Unit lty n ctx " genEquasFailure {} " : trace)

isNonExpansible :: LTerm -> Bool
isNonExpansible (LInt _) = True
isNonExpansible (Abs _ _) = True
isNonExpansible Unit = True
isNonExpansible (Let _ val body) =
  isNonExpansible val && isNonExpansible body
isNonExpansible (App Fix l) =
  isNonExpansible l
isNonExpansible (App Hd l) =
  isNonExpansible l
isNonExpansible (App Tl l) =
  isNonExpansible l
isNonExpansible (App Deref l) =
  isNonExpansible l
isNonExpansible (IfZ _ y z) =
  isNonExpansible y && isNonExpansible z
isNonExpansible (IfE _ y z) =
  isNonExpansible y && isNonExpansible z
isNonExpansible _ = False

getFreeVars :: [String] -> LType -> [String]
getFreeVars context (TVar x) =
  [x | x `notElem` context]
getFreeVars context (TArrow x y) =
  getFreeVars context x ++ getFreeVars context y
getFreeVars context (TList t) =
  getFreeVars context t
getFreeVars context (TPoly v t) =
  getFreeVars (v : context) t
getFreeVars context (TRef v) =
  getFreeVars context v
getFreeVars context (WVT _ lty) =
  getFreeVars context lty
getFreeVars _ (WVF str) =
  [str]
getFreeVars context (WF b str lty)
  | b = getFreeVars context lty
  | otherwise = getFreeVars (str : context) lty
getFreeVars _ _ = []

generalise :: Map String LType -> LType -> LType
generalise _ t =
  let fvs = getFreeVars [] t
   in List.foldr TPoly t fvs

weakGeneraliseRec :: [String] -> LType -> LType
weakGeneraliseRec (x : xs) lte =
  let newx = "_" ++ x
   in weakGeneraliseRec xs (WF False newx (subs x (WVF newx) lte))
weakGeneraliseRec [] lte = lte

weakGeneralise :: LType -> LType
weakGeneralise lte =
  weakGeneraliseRec (getFreeVars [] lte) lte

subs :: String -> LType -> LType -> LType
subs x newLTy (TVar y)
  | x == y = newLTy
  | otherwise = TVar y
subs x newLTy (TArrow lty1 lty2) =
  TArrow (subs x newLTy lty1) (subs x newLTy lty2)
subs x newLTy (TList lty) =
  TList (subs x newLTy lty)
subs x newLTy (TPoly v lty) =
  TPoly v (subs x newLTy lty)
subs x newLTy (TRef lty) =
  TRef (subs x newLTy lty)
subs x newLTy (WVT _ lty) =
  subs x newLTy lty
subs x newLTy (WF _ _ lty) =
  subs x newLTy lty
subs _ _ x = x

subsInLTyEq :: String -> LType -> LTypeEqua -> LTypeEqua
subsInLTyEq x newLTy (LTypeEqua lty1 lty2) =
  LTypeEqua (subs x newLTy lty1) (subs x newLTy lty2)

data UnifStepRes
  = UnifStepSuccess (Map String LType) [LTypeEqua]
  | UnifStepFailure String
  deriving (Show)

unificationStep :: [LTypeEqua] -> LType -> Int -> Map String LType -> UnifStepRes
unificationStep ((LTypeEqua (TArrow ltya1 ltyb1) (TArrow ltya2 ltyb2)) : tl2) ltyf n ctx
  | TArrow ltya1 ltyb1 == TArrow ltya2 ltyb2 = unificationStep tl2 ltyf n ctx
  | otherwise --UnifStepSuccess (LTypeEqua ltya1 ltya2 : LTypeEqua ltyb1 ltyb2 : tl2)
    =
    UnifStepSuccess ctx (LTypeEqua ltya1 ltya2 : LTypeEqua ltyb1 ltyb2 : tl2)
unificationStep ((LTypeEqua (TPoly v lty) td) : tl2) _ n ctx
  | TPoly v lty == td = UnifStepSuccess ctx tl2
  | otherwise =
    let (_, newlty) = alphaConvTypes lty Map.empty n
     in UnifStepSuccess ctx (LTypeEqua newlty td : tl2)
unificationStep ((LTypeEqua tg (TPoly v lty)) : tl2) _ n ctx
  | TPoly v lty == tg = UnifStepSuccess ctx tl2
  | otherwise =
    let (_, newlty) = alphaConvTypes lty Map.empty n
     in UnifStepSuccess ctx (LTypeEqua tg newlty : tl2)
unificationStep ((LTypeEqua (TList lty1) (TList lty2)) : tl2) _ _ ctx
  | lty1 == lty2 = UnifStepSuccess ctx tl2
  | otherwise = UnifStepSuccess ctx (LTypeEqua lty1 lty2 : tl2)
unificationStep (LTypeEqua (WF b v lty) td : tl2) _ _ ctx
  | WF b v lty == td = UnifStepSuccess ctx tl2
  | otherwise = UnifStepSuccess ctx (LTypeEqua lty td : tl2)
unificationStep (LTypeEqua tg (WF b v lty) : tl2) _ _ ctx
  | WF b v lty == tg = UnifStepSuccess ctx tl2
  | otherwise = UnifStepSuccess ctx (LTypeEqua lty tg : tl2)
unificationStep (LTypeEqua (WVT str lty) td : tl2) _ _ ctx
  | WVT str lty == td = UnifStepSuccess ctx tl2 
  --UnifStepSuccess ctx (LTypeEqua lty td : tl2)
  | otherwise = UnifStepSuccess ctx (LTypeEqua lty td : tl2)
{-
  case Map.lookup str ctx of
    Nothing -> error "WEIRD 11 ?!"
    Just nlty ->
      if nlty == lty
        then UnifStepSuccess ctx (LTypeEqua lty td : tl2)
        else error "WEIRD 12 ?!"
-}
unificationStep (LTypeEqua tg (WVT str lty) : tl2) _ _ ctx
  | WVT str lty == tg = UnifStepSuccess ctx tl2 --UnifStepSuccess ctx (LTypeEqua lty tg : tl2)
  | otherwise = UnifStepSuccess ctx (LTypeEqua lty tg : tl2)
{-
  case Map.lookup str ctx of
    Nothing -> error "WEIRD 21 ?!"
    Just nlty ->
      if nlty == lty
        then UnifStepSuccess ctx (LTypeEqua tg lty : tl2)
        else error "WEIRD 22 ?!"
-}

unificationStep (LTypeEqua (WVF str) td : tl2) _ _ ctx
  | WVF str == td = UnifStepSuccess ctx tl2 --UnifStepSuccess (Map.insert str td ctx) (LTypeEqua (WVT str td) td : tl2)
  | occurCheck (TVar str) td = UnifStepFailure ("WVF : " ++ show str ++ " 3 occurs in " ++ show td)
  | otherwise =
    case Map.lookup str ctx of
      Nothing -> UnifStepSuccess (Map.insert str td ctx) (LTypeEqua (WVT str td) td : tl2)
      Just nlty -> UnifStepSuccess ctx (LTypeEqua nlty td : tl2)
unificationStep (LTypeEqua tg (WVF str) : tl2) _ _ ctx
  | WVF str == tg = UnifStepSuccess ctx tl2
  | occurCheck (TVar str) tg = UnifStepFailure ("WVF : " ++ show str ++ " 4 occurs in " ++ show tg) --(show (LTypeEqua (WV b v lty) td : tl2) : trace)
  | otherwise --UnifStepSuccess (Map.insert str tg ctx) (LTypeEqua (WVT str tg) tg : tl2)
    =
    case Map.lookup str ctx of
      Nothing -> UnifStepSuccess (Map.insert str tg ctx) (LTypeEqua (WVT str tg) tg : tl2)
      Just nlty -> UnifStepSuccess ctx (LTypeEqua nlty tg : tl2)
unificationStep ((LTypeEqua (TRef lty1) (TRef lty2)) : tl2) _ _ ctx
  | lty1 == lty2 = UnifStepSuccess ctx tl2
  | otherwise = UnifStepSuccess ctx (LTypeEqua lty1 lty2 : tl2)
unificationStep ((LTypeEqua (TVar x) td) : tl2) ltyf _ ctx
  | occurCheck ltyf (TVar x) || occurCheck ltyf td = UnifStepSuccess ctx (tl2 ++ [LTypeEqua (TVar x) td])
  | TVar x == td = UnifStepSuccess ctx tl2
  | occurCheck (TVar x) td = UnifStepFailure (x ++ " 1 occurs in " ++ show td) -- (show (LTypeEqua (TVar x) td : tl2) : trace) -- ++ "     ***  " ++ show ((LTypeEqua (TVar x) td) : tl2) ++ " ***")
  | otherwise = UnifStepSuccess ctx (List.map (subsInLTyEq x td) tl2)
unificationStep ((LTypeEqua tg (TVar x)) : tl2) ltyf _ ctx
  | occurCheck ltyf tg || occurCheck ltyf (TVar x) = UnifStepSuccess ctx (tl2 ++ [LTypeEqua tg (TVar x)])
  | TVar x == tg = UnifStepSuccess ctx tl2
  | occurCheck (TVar x) tg = UnifStepFailure (x ++ " 2 occurs in " ++ show tg) --(show (LTypeEqua tg (TVar x) : tl2) : trace)
  | otherwise = UnifStepSuccess ctx (List.map (subsInLTyEq x tg) tl2)
unificationStep ((LTypeEqua x y) : l) _ _ ctx
  | x == y = UnifStepSuccess ctx l
  | otherwise = UnifStepFailure (show x ++ " is incompatible with " ++ show y) --(show ((LTypeEqua x y) : l) : trace)
unificationStep [] _ _ _ = UnifStepFailure "Empty list"

showEqL :: [LTypeEqua] -> String
showEqL = List.foldr ((++) . show) " "

show2EqLs :: ([LTypeEqua], [LTypeEqua]) -> String
show2EqLs (l1, l2) = showEqL l1 ++ "\n ### \n" ++ showEqL l2

data UnificationRes
  = UnifSuccess [String] LTypeEqua
  | UnifFailure [String] String --[String]
  deriving (Show)

{-
  Only works on the last equation in a sequence of equations
  The equation must contain a type variable that represents the type
  we are trying to guess
-}
isSimplifiable :: LTypeEqua -> Bool
isSimplifiable (LTypeEqua (TArrow _ _) (TArrow _ _)) = True
isSimplifiable (LTypeEqua (TList _) (TList _)) = True
isSimplifiable (LTypeEqua (TRef _) (TRef _)) = True
isSimplifiable (LTypeEqua WF {} _) = True
isSimplifiable (LTypeEqua _ WF {}) = True
isSimplifiable (LTypeEqua WVT {} _) = True
isSimplifiable (LTypeEqua _ WVT {}) = True
isSimplifiable (LTypeEqua WVF {} _) = True
isSimplifiable (LTypeEqua _ WVF {}) = True
isSimplifiable (LTypeEqua (TPoly _ _) _) = True
isSimplifiable (LTypeEqua _ (TPoly _ _)) = True
isSimplifiable _ = False

unifyEqs :: [LTypeEqua] -> [String] -> LType -> Int -> Map String LType -> UnificationRes
unifyEqs [x] strl lty n ctx
  | isSimplifiable x =
    case unificationStep [x] lty n ctx of
      UnifStepSuccess ctx newl ->
        unifyEqs newl (show newl : strl) lty n ctx
      UnifStepFailure msg -> UnifFailure strl (" 1 Unification failure (unifyEqs) : " ++ msg ++ "\n" ++ show (List.reverse strl))
  | otherwise = UnifSuccess strl x
unifyEqs l strl lty n ctx =
  case unificationStep l lty n ctx of
    UnifStepSuccess ctx newl ->
      unifyEqs newl (show newl : strl) lty n ctx
    UnifStepFailure msg -> UnifFailure strl (" 2 Unification failure (unifyEqs) : " ++ msg ++ "\n" ++ show (List.reverse strl))

getType :: LTypeEqua -> LType -> LType
getType (LTypeEqua x y) lty
  | x == lty = y
  | y == lty = x
  | otherwise = error (show lty ++ " not present in " ++ show (LTypeEqua x y))

data TypeInferenceRes
  = TypeInferenceSuccess [String] LTerm LType [String]
  | TypeInferenceFailure [String] LTerm String [String]

instance Show TypeInferenceRes where
  show (TypeInferenceSuccess l lte lty trace) =
    "Type inference of : " ++ show lte ++ "\n\n"
      ++ List.intercalate "\n" l
      ++ "\n\n"
      ++ "Type inference of : "
      ++ show lte
      ++ " resulted in : "
      ++ show lty
      ++ "\n trace : \n"
      ++ List.intercalate "" (List.reverse trace)
  show (TypeInferenceFailure l lte msg trace) =
    "Type inference of : " ++ show lte ++ "\n\n"
      ++ List.intercalate "\n" l
      ++ "\n\n"
      ++ "Type inference of : "
      ++ show lte
      ++ " failed : "
      ++ msg
      ++ "\n trace : \n"
      ++ List.intercalate "" trace

typeInferenceRec :: LTerm -> Map String LType -> TypeInferenceRes
typeInferenceRec lte context =
  let lty = TVar "T0"
   in case genEquas lte lty (GenEquasContext 1 context) [mkString lte lty 1 context []] of
        GenEquasFailed msg trace ->
          TypeInferenceFailure [] lte msg (List.reverse trace)
        GenEquasSuccess n eqs trace ->
          case unifyEqs eqs [show eqs] lty n Map.empty of
            UnifSuccess strl resEq ->
              TypeInferenceSuccess
                (List.reverse strl)
                lte
                (getType resEq lty)
                (List.reverse trace)
            UnifFailure strl msg ->
              TypeInferenceFailure (List.reverse strl) lte msg (List.reverse trace)

typeInference :: LTerm -> TypeInferenceRes
typeInference lte = typeInferenceRec lte Map.empty