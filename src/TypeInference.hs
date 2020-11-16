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
occurCheck tyv (WVT lty) =
  tyv == WVT lty || occurCheck tyv lty
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
alphaConvTypes (WVT lty) ctx n =
  let (newn, newlty) = alphaConvTypes lty ctx n
   in (newn, WVT newlty)
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

data GenEquasRes
  = GenEquasSuccess (Map String LType) [LTypeEqua] Int [String]
  | GenEquasFailed String [String]

-- (WVF, [WVT|V...])
data InferenceContext
  = InferenceContext Int (Map String LType)

getGRReqs :: GenEquasRes -> [LTypeEqua]
getGRReqs (GenEquasSuccess _ eqs _ _) = eqs
getGRReqs _ = error "errroooooooooor"

instance Show GenEquasRes where
  show (GenEquasSuccess weakrvs eqs n strl) =
    "GenEquasSuccess : \n"
      ++ "    Eqs : \n"
      ++ show eqs
      ++ "\n n : \n"
      ++ show n
      ++ "     strl : \n"
      ++ List.intercalate "" strl
      ++ " \n weakvrinsts : \n"
      ++ show weakrvs
  show (GenEquasFailed str strl) =
    "GenEquasFailed : \n"
      ++ "    cause : "
      ++ str
      ++ "\n     strl : \n"
      ++ List.intercalate "\n" strl
      ++ "\n"

termListToEquaList :: [LTerm] -> LType -> Int -> Map String LType -> Map String LType -> [String] -> GenEquasRes
termListToEquaList (x : xs) lty n ctx weakvs trace =
  case genEquas x lty n ctx weakvs trace of --(mget x lty n ctx trace) of
    GenEquasFailed msg trace1 -> GenEquasFailed msg trace1
    GenEquasSuccess weakvs1 lteqs1 newN1 trace1 ->
      case termListToEquaList xs lty newN1 ctx weakvs1 trace1 of --(mgetl xs lty newN1 ctx trace) of
        GenEquasFailed msg trace2 -> GenEquasFailed msg trace2
        GenEquasSuccess weakvs2 lteqs2 newN2 trace2 ->
          GenEquasSuccess weakvs2 (lteqs1 ++ lteqs2) newN2 trace2
termListToEquaList [] _ n _ weakvs trace = GenEquasSuccess weakvs [] n trace

genEquas :: LTerm -> LType -> Int -> Map String LType -> Map String LType -> [String] -> GenEquasRes
genEquas (Var x) lty n context weakvs trace =
  case Map.lookup x context of
    Just ltyv ->
      GenEquasSuccess weakvs [LTypeEqua lty ltyv] n (mkString (Var x) lty n context (show (LTypeEqua lty ltyv)) : trace)
    --(aett (LTypeEqua lty ltyv) trace)
    Nothing ->
      GenEquasFailed " genEquasFailure (Var x) " (mkString (Var x) lty n context " genEquasFailure (Var x) " : trace)
genEquas (Abs v bodyLTe) lty n context weakvs trace =
  let ltya = TVar ("T" ++ show n)
   in let ltyr = TVar ("T" ++ show (n + 1))
       in let newContext = Map.insert v ltya context
           in case genEquas bodyLTe ltyr (n + 2) newContext weakvs trace of
                GenEquasSuccess weakvs1 newLTyEqs newN trace1 ->
                  GenEquasSuccess weakvs1 (LTypeEqua lty (TArrow ltya ltyr) : newLTyEqs) newN (mkString (Abs v bodyLTe) lty n context (show (LTypeEqua lty (TArrow ltya ltyr))) : trace1)
                GenEquasFailed msg trace1 -> GenEquasFailed msg trace1
genEquas (App Fix (Abs v body)) lty n context weakvs trace =
  let tfix = TVar ("T" ++ show n)
   in case genEquas body tfix (n + 1) (Map.insert v tfix context) weakvs trace of
        GenEquasSuccess weakvs1 newEqs newN trace1 -> GenEquasSuccess weakvs1 (LTypeEqua lty tfix : newEqs) newN (mkString (App Fix (Abs v body)) lty n context (show (LTypeEqua lty tfix)) : trace1)
        GenEquasFailed msg trace1 -> GenEquasFailed msg trace1
genEquas (App lte1 lte2) lty n context weakvs trace =
  let ltya = TVar ("T" ++ show n)
   in case genEquas lte1 (TArrow ltya lty) (n + 1) context weakvs trace of
        GenEquasFailed msg trace1 -> GenEquasFailed msg trace1
        GenEquasSuccess weakvs1 newLTyEquas1 newN1 trace1 ->
          case genEquas lte2 ltya newN1 context weakvs1 trace1 of
            GenEquasFailed msg trace2 ->
              GenEquasFailed msg trace2
            GenEquasSuccess weakvs2 newLTyEquas2 newN2 trace2 ->
              GenEquasSuccess weakvs2 (newLTyEquas1 ++ newLTyEquas2) newN2 (mkString (App lte1 lte2) lty n context (show (newLTyEquas1 ++ newLTyEquas2)) : trace2)
genEquas (LInt x) lty n context weakvs trace =
  GenEquasSuccess weakvs [LTypeEqua lty TInt] n (mkString (LInt x) lty n context (show (LTypeEqua lty TInt)) : trace)
genEquas (List l) lty n ctx weakvs trace =
  let newTV = TVar ("T" ++ show n)
      newEqua = LTypeEqua lty (TList newTV)
   in case termListToEquaList l newTV (n + 1) ctx weakvs trace of
        GenEquasFailed msg trace1 -> GenEquasFailed msg trace1
        GenEquasSuccess weakvs1 lteqs newN trace1 ->
          GenEquasSuccess weakvs1 (newEqua : lteqs) newN (mkString (List l) lty n ctx (show newEqua) : trace1)
genEquas (IfZ lte1 lte2 lte3) lty n context weakvs trace =
  let newT = TVar ("T" ++ show n)
   in case genEquas lte1 TInt (n + 1) context weakvs trace of
        GenEquasFailed msg trace1 -> GenEquasFailed msg trace1
        GenEquasSuccess weakvs1 newEqs1 newN1 trace1 ->
          case genEquas lte2 newT newN1 context weakvs1 trace1 of
            GenEquasFailed msg trace2 -> GenEquasFailed msg trace2
            GenEquasSuccess weakvs2 newEqs2 newN2 trace2 ->
              case genEquas lte3 newT newN2 context weakvs2 trace2 of
                GenEquasFailed msg trace3 -> GenEquasFailed msg trace3
                GenEquasSuccess weakvs3 newEqs3 newN3 trace3 ->
                  GenEquasSuccess
                    weakvs3
                    (LTypeEqua lty newT : (newEqs1 ++ newEqs2 ++ newEqs3))
                    newN3
                    (mkString (IfZ lte1 lte2 lte3) lty n context (show (LTypeEqua lty newT : (newEqs1 ++ newEqs2 ++ newEqs3))) : trace3) --(aett (LTypeEqua lty newT) trace3)
genEquas (IfE lte1 lte2 lte3) lty n context weakvs trace =
  let newTa = TVar ("T" ++ show n)
      newTn = TVar ("T" ++ show (n + 1))
   in case genEquas lte1 (TList newTa) (n + 2) context weakvs trace of
        GenEquasFailed msg trace1 -> GenEquasFailed msg trace1
        GenEquasSuccess weakvs1 newEqs1 newN1 trace1 ->
          case genEquas lte2 newTn newN1 context weakvs1 trace1 of
            GenEquasFailed msg trace2 -> GenEquasFailed msg trace2
            GenEquasSuccess weakvs2 newEqs2 newN2 trace2 ->
              case genEquas lte3 newTn newN2 context weakvs2 trace2 of
                GenEquasFailed msg trace3 -> GenEquasFailed msg trace3
                GenEquasSuccess weakvs3 newEqs3 newN3 trace3 ->
                  GenEquasSuccess
                    weakvs3
                    (LTypeEqua lty newTn : (newEqs1 ++ newEqs2 ++ newEqs3))
                    newN3
                    (mkString (IfE lte1 lte2 lte3) lty n context (show (LTypeEqua lty newTn : (newEqs1 ++ newEqs2 ++ newEqs3))) : trace3)
genEquas (Let v lte1 lte2) lty n context weakvs trace =
  case typeInferenceRec lte1 context weakvs of
    TypeInferenceSuccess weakvs1 _ _ newLTy newtrace ->
      if isNonExpansible lte1
        then
          let newContext = Map.insert v (generalise context newLTy) context
           in genEquas lte2 lty n (updateCtx (Map.toList weakvs1) newContext) weakvs1 ([" {{{{{{ " ++ show weakvs1 ++ "  }}}}}}   "] ++ trace ++ newtrace)
        else
          let newContext = Map.insert v (weakGeneralise newLTy) context
           in genEquas lte2 lty n (updateCtx (Map.toList weakvs1) newContext) weakvs1 ([" {{{{{{ " ++ show weakvs1 ++ "  }}}}}}   "] ++ trace ++ newtrace)
    TypeInferenceFailure _ _ _ newtrace ->
      GenEquasFailed (" genEquasFailure {1} typeDetection of " ++ show lte1 ++ " in " ++ show context) (mkString Unit lty n context (" genEquasFailure {1} typeDetection of " ++ show lte1 ++ " in " ++ show context) : trace ++ newtrace)
genEquas Add lty n context weakvs trace =
  GenEquasSuccess weakvs [LTypeEqua lty (TArrow TInt (TArrow TInt TInt))] n (mkString Add lty n context (show (LTypeEqua lty (TArrow TInt (TArrow TInt TInt)))) : trace)
genEquas Sub lty n context weakvs trace =
  GenEquasSuccess weakvs [LTypeEqua lty (TArrow TInt (TArrow TInt TInt))] n (mkString Sub lty n context (show (LTypeEqua lty (TArrow TInt (TArrow TInt TInt)))) : trace)
genEquas Cons lty n context weakvs trace =
  let newV = "T" ++ show n
      newT = TVar newV
   in GenEquasSuccess
        weakvs
        [LTypeEqua (TPoly newV (TArrow newT (TArrow (TList newT) (TList newT)))) lty]
        (n + 1)
        (mkString Cons lty n context (show (LTypeEqua (TPoly newV (TArrow newT (TArrow (TList newT) (TList newT)))) lty)) : trace)
genEquas Hd lty n context weakvs trace =
  let newV = "T" ++ show n
      newT = TVar newV
   in GenEquasSuccess
        weakvs
        [LTypeEqua (TPoly newV (TArrow (TList newT) newT)) lty]
        (n + 1)
        (mkString Hd lty n context (show (LTypeEqua (TPoly newV (TArrow (TList newT) newT)) lty)) : trace)
genEquas Tl lty n context weakvs trace =
  let newV = "T" ++ show n
      newT = TVar newV
   in GenEquasSuccess
        weakvs
        [LTypeEqua (TPoly newV (TArrow (TList newT) (TList newT))) lty]
        (n + 1)
        (mkString Tl lty n context (show (LTypeEqua (TPoly newV (TArrow (TList newT) newT)) lty)) : trace)
genEquas Ref lty n context weakvs trace =
  let newV = "T" ++ show n
      newT = TPoly newV (TArrow (TVar newV) (TRef (TVar newV)))
   in GenEquasSuccess weakvs [LTypeEqua lty newT] (n + 1) (mkString Ref lty n context (show (LTypeEqua lty newT)) : trace)
genEquas Deref lty n context weakvs trace =
  let newV = "T" ++ show n
      newT = TPoly newV (TArrow (TRef (TVar newV)) (TVar newV))
   in GenEquasSuccess weakvs [LTypeEqua lty newT] (n + 1) (mkString Deref lty n context (show (LTypeEqua lty newT)) : trace)
genEquas Assign lty n context weakvs trace =
  let newV = "T" ++ show n
      newT = TPoly newV (TArrow (TRef (TVar newV)) (TArrow (TVar newV) TUnit))
   in GenEquasSuccess weakvs [LTypeEqua lty newT] (n + 1) (mkString Assign lty n context (show (LTypeEqua lty newT)) : trace)
genEquas Unit lty n context weakvs trace =
  GenEquasSuccess weakvs [LTypeEqua lty TUnit] n (mkString Unit lty n context (show (LTypeEqua lty TUnit)) : trace)
genEquas _ lty n context _ trace =
  GenEquasFailed " genEquasFailure {} " (mkString Unit lty n context " genEquasFailure {} " : trace)

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
getFreeVars context (WVT lty) =
  getFreeVars context lty
getFreeVars _ (WVF str) = [str]
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
subs x newLTy (WVT lty) =
  subs x newLTy lty
--
subs x newLTy (WVF str)
  | x == str = newLTy
  | otherwise = WVF str
--
subs x newLTy (WF True _ lty) =
  subs x newLTy lty
--
subs x newLTy (WF False str lty)
  | x == str = WF True str (subs x newLTy lty)
  | otherwise = WF False str (subs x newLTy lty)
subs _ _ x = x

{-
subsLTy :: LType -> LType -> LType -> LType
subsLTy ltyts newlty (TArrow lty1 lty2)
  | ltyts == TArrow lty1 lty2 = newlty
  | otherwise = TArrow (subsLTy ltyts newlty lty1) (subsLTy ltyts newlty lty2)
subsLTy ltyts newlty (TList lty)
  | ltyts == TList lty = newlty
  | otherwise = TList (subsLTy ltyts newlty lty)
subsLTy ltyts newlty (TPoly str lty)
  | ltyts == TPoly str lty = newlty
  | otherwise = TPoly str (subsLTy ltyts newlty lty)
subsLTy ltyts newlty (TRef lty)
  | ltyts == TRef lty = newlty
  | otherwise = TRef (subsLTy ltyts newlty lty)
subsLTy (WVF str1) (WVT lty1) (WF b str2 lty2)
  | str1 == str2 = WF True str2 (subsLTy (WVF str1) (WVT lty1) lty2)
  | otherwise = WF b str2 (subsLTy (WVF str1) (WVT lty1) lty2)
subsLTy ltyts newlty (WF b str2 lty2)
  | ltyts == WF b str2 lty2 = newlty
  | otherwise = WF b str2 (subsLTy ltyts newlty lty2)
subsLTy ltyts newlty lty
  | ltyts == lty = newlty
  | otherwise = lty

subsLTyInLTyEq :: LType -> LType -> LTypeEqua -> LTypeEqua
subsLTyInLTyEq ltyts newlty (LTypeEqua lty1 lty2) =
  LTypeEqua (subsLTy ltyts newlty lty1) (subsLTy ltyts newlty lty2)
-}

subsInLTyEq :: String -> LType -> LTypeEqua -> LTypeEqua
subsInLTyEq x newLTy (LTypeEqua lty1 lty2) =
  LTypeEqua (subs x newLTy lty1) (subs x newLTy lty2)

data UnifStepRes
  = UnifStepSuccess (Map String LType) [LTypeEqua]
  | UnifStepFailure String
  deriving (Show)

gelfusr :: UnifStepRes -> [LTypeEqua]
gelfusr (UnifStepSuccess _ l) = l
gelfusr _ = error "rezrezrez"

unificationStep :: [LTypeEqua] -> LType -> Int -> Map String LType -> UnifStepRes
unificationStep ((LTypeEqua (TArrow ltya1 ltyb1) (TArrow ltya2 ltyb2)) : tl2) ltyf n weakvs
  | TArrow ltya1 ltyb1 == TArrow ltya2 ltyb2 = unificationStep tl2 ltyf n weakvs
  | otherwise --UnifStepSuccess (LTypeEqua ltya1 ltya2 : LTypeEqua ltyb1 ltyb2 : tl2)
    =
    UnifStepSuccess weakvs (LTypeEqua ltya1 ltya2 : LTypeEqua ltyb1 ltyb2 : tl2)
unificationStep ((LTypeEqua (TPoly v lty) td) : tl2) _ n weakvs
  | TPoly v lty == td = UnifStepSuccess weakvs tl2
  | otherwise =
    let (_, newlty) = alphaConvTypes lty Map.empty n
     in UnifStepSuccess weakvs (LTypeEqua newlty td : tl2)
unificationStep ((LTypeEqua tg (TPoly v lty)) : tl2) _ n weakvs
  | TPoly v lty == tg = UnifStepSuccess weakvs tl2
  | otherwise =
    let (_, newlty) = alphaConvTypes lty Map.empty n
     in UnifStepSuccess weakvs (LTypeEqua tg newlty : tl2)
unificationStep ((LTypeEqua (TList lty1) (TList lty2)) : tl2) _ _ weakvs
  | lty1 == lty2 = UnifStepSuccess weakvs tl2
  | otherwise = UnifStepSuccess weakvs (LTypeEqua lty1 lty2 : tl2)
unificationStep (LTypeEqua (WF b v lty) td : tl2) _ _ weakvs
  | WF b v lty == td = UnifStepSuccess weakvs tl2
  | otherwise = UnifStepSuccess weakvs (LTypeEqua lty td : tl2)
unificationStep (LTypeEqua tg (WF b v lty) : tl2) _ _ weakvs
  | WF b v lty == tg = UnifStepSuccess weakvs tl2
  | otherwise = UnifStepSuccess weakvs (LTypeEqua lty tg : tl2)
unificationStep (LTypeEqua (WVT lty) td : tl2) _ _ weakvs
  | WVT lty == td = UnifStepSuccess weakvs tl2
  | otherwise = UnifStepSuccess weakvs (LTypeEqua lty td : tl2)
unificationStep (LTypeEqua (WVF str) td : tl2) _ _ weakvs
  | WVF str == td = UnifStepSuccess weakvs tl2
  | occurCheck (TVar str) td = UnifStepFailure ("WVF : " ++ show str ++ " 3 occurs in " ++ show td) --(show (LTypeEqua (WV b v lty) td : tl2) : trace)
  | otherwise = UnifStepSuccess (Map.insert str td weakvs) (LTypeEqua (WVT td) td : tl2)
unificationStep (LTypeEqua tg (WVT lty) : tl2) _ _ weakvs
  | WVT lty == tg = UnifStepSuccess weakvs tl2
  | otherwise = UnifStepSuccess weakvs (LTypeEqua lty tg : tl2)
unificationStep (LTypeEqua tg (WVF str) : tl2) _ _ weakvs
  | WVF str == tg = UnifStepSuccess weakvs tl2
  | occurCheck (TVar str) tg = UnifStepFailure ("WVF : " ++ show str ++ " 4 occurs in " ++ show tg) --(show (LTypeEqua (WV b v lty) td : tl2) : trace)
  | otherwise = UnifStepSuccess (Map.insert str tg weakvs) (LTypeEqua (WVT tg) tg : tl2)
unificationStep ((LTypeEqua (TRef lty1) (TRef lty2)) : tl2) _ _ weakvs
  | lty1 == lty2 = UnifStepSuccess weakvs tl2
  | otherwise = UnifStepSuccess weakvs (LTypeEqua lty1 lty2 : tl2)
unificationStep ((LTypeEqua (TVar x) td) : tl2) ltyf _ weakvs
  | occurCheck ltyf (TVar x) || occurCheck ltyf td = UnifStepSuccess weakvs (tl2 ++ [LTypeEqua (TVar x) td])
  | TVar x == td = UnifStepSuccess weakvs tl2
  | occurCheck (TVar x) td = UnifStepFailure (x ++ " 1 occurs in " ++ show td) -- (show (LTypeEqua (TVar x) td : tl2) : trace) -- ++ "     ***  " ++ show ((LTypeEqua (TVar x) td) : tl2) ++ " ***")
  | otherwise = UnifStepSuccess weakvs (List.map (subsInLTyEq x td) tl2)
unificationStep ((LTypeEqua tg (TVar x)) : tl2) ltyf _ weakvs
  | occurCheck ltyf tg || occurCheck ltyf (TVar x) = UnifStepSuccess weakvs (tl2 ++ [LTypeEqua tg (TVar x)])
  | TVar x == tg = UnifStepSuccess weakvs tl2
  | occurCheck (TVar x) tg = UnifStepFailure (x ++ " 2 occurs in " ++ show tg) --(show (LTypeEqua tg (TVar x) : tl2) : trace)
  | otherwise = UnifStepSuccess weakvs (List.map (subsInLTyEq x tg) tl2)
unificationStep ((LTypeEqua x y) : l) _ _ weakvs
  | x == y = UnifStepSuccess weakvs l
  | otherwise = UnifStepFailure (show x ++ " is incompatible with " ++ show y) --(show ((LTypeEqua x y) : l) : trace)
unificationStep [] _ _ _ = UnifStepFailure "Empty list"

showEqL :: [LTypeEqua] -> String
showEqL = List.foldr ((++) . show) " "

show2EqLs :: ([LTypeEqua], [LTypeEqua]) -> String
show2EqLs (l1, l2) = showEqL l1 ++ "\n ### \n" ++ showEqL l2

data UnificationRes
  = UnifSuccess (Map String LType) [String] LTypeEqua
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
unifyEqs [x] strl lty n weakvs
  | isSimplifiable x =
    case unificationStep [x] lty n weakvs of
      UnifStepSuccess nweakvs newl ->
        unifyEqs newl (show newl : strl) lty n nweakvs
      UnifStepFailure msg -> UnifFailure strl (" 1 Unification failure (unifyEqs) : " ++ msg ++ "\n" ++ show (List.reverse strl))
  | otherwise = UnifSuccess weakvs strl x
unifyEqs l strl lty n weakvs =
  case unificationStep l lty n weakvs of
    UnifStepSuccess nweakvs newl ->
      unifyEqs newl (show newl : strl) lty n nweakvs
    UnifStepFailure msg -> UnifFailure strl (" 2 Unification failure (unifyEqs) : " ++ msg ++ "\n" ++ show (List.reverse strl))

getType :: LTypeEqua -> LType -> LType
getType (LTypeEqua x y) lty
  | x == lty = y
  | y == lty = x
  | otherwise = error (show lty ++ " not present in " ++ show (LTypeEqua x y))

data TypeInferenceRes
  = TypeInferenceSuccess (Map String LType) [String] LTerm LType [String]
  | TypeInferenceFailure [String] LTerm String [String]

instance Show TypeInferenceRes where
  show (TypeInferenceSuccess weakvs l lte lty trace) =
    "Type inference of : " ++ show lte ++ "\n\n"
      ++ List.intercalate "\n" l
      ++ "\n\n"
      ++ "Type inference of : "
      ++ show lte
      ++ " resulted in : "
      ++ show lty
      ++ "\n trace : \n"
      ++ List.intercalate "" (List.reverse trace)
      ++ "\n\n weakvs : "
      ++ show weakvs
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

updateEqs :: [(String, LType)] -> [LTypeEqua] -> [LTypeEqua]
updateEqs ((str, lty) : l) lteqs =
  updateEqs l (List.map (subsInLTyEq str lty) lteqs)
updateEqs [] lteqs = lteqs

updateCtx :: [(String, LType)] -> Map String LType -> Map String LType
updateCtx ((str, lty) : l) ctx =
  updateCtx l (Map.map (subs str lty) ctx) --l (List.map (subsInLTyEq str lty) lteqs)
updateCtx [] ctx = ctx

{-
initWV :: LType -> String -> LType -> LType
initWV newT str (WVF x)
  | str == x = newT
  | otherwise = WVF x
initWV newT str (WF False x lty)
  | str == x = initWV newT str lty
  | otherwise = WF False x (initWV newT str lty)
initWV newT str (WF True x lty)
  | str == x = error "initWV : var already initialized"
  | otherwise = WF False x (initWV newT str lty)
-}

{-
innerTypeInferenceRec :: LTerm -> Map String LType -> Map String LType -> TypeInferenceRes
innerTypeInferenceRec lte vcontext weakvs =
  let lty = TVar "T0"
   in case genEquas lte lty 1 vcontext [mkString lte lty 1 vcontext []] of
        GenEquasFailed msg trace ->
          TypeInferenceFailure [] lte msg (List.reverse trace)
        GenEquasSuccess eqs n trace ->
          case unifyEqs eqs [show eqs] lty n weakvs of
            UnifSuccess weakvs1 strl resEq ->
              TypeInferenceSuccess
                weakvs1
                (List.reverse strl)
                lte
                (getType resEq lty)
                (List.reverse trace)
            UnifFailure strl msg ->
              TypeInferenceFailure (List.reverse strl) lte msg (List.reverse trace)
-}
typeInferenceRec :: LTerm -> Map String LType -> Map String LType -> TypeInferenceRes
typeInferenceRec lte vcontext weakvs =
  let lty = TVar "T0"
   in case genEquas lte lty 1 vcontext weakvs [mkString lte lty 1 vcontext []] of
        GenEquasFailed msg trace ->
          TypeInferenceFailure [] lte msg (List.reverse trace)
        GenEquasSuccess weakvs1 eqs n trace ->
          -- apply changes from weakvs to eqs before unifying
          case unifyEqs (updateEqs (Map.toList weakvs1) eqs) [show eqs] lty n weakvs1 of
            UnifSuccess weakvs2 strl resEq ->
              TypeInferenceSuccess
                weakvs2
                (List.reverse strl)
                lte
                (getType resEq lty)
                (List.reverse trace)
            UnifFailure strl msg ->
              TypeInferenceFailure (List.reverse strl) lte msg (List.reverse trace)

typeInference :: LTerm -> TypeInferenceRes
typeInference lte = typeInferenceRec lte Map.empty Map.empty

{-

-}