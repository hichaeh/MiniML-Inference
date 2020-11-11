module Types where

import Data.List as List
import Data.Map as Map (Map, fromList, insert, keys, lookup)
import Terms

data LType
  = TVar String
  | TArrow LType LType
  | TList LType
  | TPoly String LType
  | TRef LType
  | TInt
  | TUnit
  | WV Bool String LType
  | WF Bool String LType
  deriving (Eq)

instance Show LType where
  show (TVar v) = v
  show (TArrow srct destt) = (show srct) ++ " -> " ++ (show destt)
  show (TList x) = "[" ++ (show x) ++ "]"
  show (TPoly x y) = "∀" ++ x ++ "." ++ show y
  show (TRef x) = "Ref ( " ++ show x ++ " )"
  show TInt = "ℕ"
  show TUnit = "⬤"
  show (WV True _ lty) = show lty
  show (WV False str _) = str
  show (WF True _ lty) = show lty
  show (WF False str lty) = "∀" ++ str ++ "." ++ show lty

data LTypeEqua = LTypeEqua LType LType deriving (Eq)

instance Show LTypeEqua where
  show (LTypeEqua lty1 lty2) = (show lty1) ++ " = " ++ (show lty2)

occurCheck :: String -> LType -> Bool
occurCheck v (TVar x) = v == x
occurCheck v (TArrow lty1 lty2) = occurCheck v lty1 || occurCheck v lty2
occurCheck v (TList ltype) = occurCheck v ltype
occurCheck v (TPoly _ ltype) = occurCheck v ltype
occurCheck v (TRef x) = occurCheck v x
occurCheck v (WV b str lty)
  | b == True = occurCheck v lty
  | otherwise = str == v
occurCheck v (WF _ _ lty) = occurCheck v lty
occurCheck _ _ = False

occurCheck2 :: LType -> LType -> Bool
occurCheck2 (TVar x) (TVar y) = x == y
occurCheck2 v (TArrow lty1 lty2) = v == (TArrow lty1 lty2) || occurCheck2 v lty1 || occurCheck2 v lty2
occurCheck2 v (TList ltype) = v == (TList ltype) || occurCheck2 v ltype
occurCheck2 v (TPoly x ltype) = v == (TPoly x ltype) || occurCheck2 v ltype
occurCheck2 v (TRef x) = v == (TRef x) || occurCheck2 v x
occurCheck2 v (WV True str lty) = v == (WV True str lty) || (occurCheck2 v lty)
occurCheck2 v (WV False str lty) = v == (WV False str lty) || (TVar str) == v
occurCheck2 v (WF b x lty) = v == (WF b x lty) || occurCheck2 v lty
occurCheck2 _ _ = False

alphaConvTypes :: LType -> Map String String -> Int -> (Int, LType)
alphaConvTypes (TVar x) ctx n =
  case (Map.lookup x ctx) of
    Just y -> (n, TVar y)
    Nothing -> (n, TVar x)
alphaConvTypes (WV b str lty) ctx n
  | b == True =
    let (newn, newlty) = alphaConvTypes lty ctx n
     in (newn, (WV True str newlty))
  | otherwise =
    case (Map.lookup str ctx) of
      Just y -> (n, (WV False y lty))
      Nothing -> (n, (WV False str lty))
alphaConvTypes (TArrow x y) ctx n =
  let (newn1, newlty1) = alphaConvTypes x ctx n
      (newn2, newlty2) = alphaConvTypes y ctx newn1
   in (newn2, TArrow newlty1 newlty2)
alphaConvTypes (TList lty) ctx n =
  let (newn, newlty) = alphaConvTypes lty ctx n
   in (newn, TList newlty)
alphaConvTypes (TRef lty) ctx n =
  let (newn, newlty) = alphaConvTypes lty ctx n
   in (newn, newlty)
alphaConvTypes (TPoly str lty) ctx n =
  let newT = "T" ++ show n
      (newn, newlty) = alphaConvTypes lty (Map.insert str newT ctx) (n + 1)
   in (newn, TPoly newT newlty)
alphaConvTypes (WF b x lty) ctx n
  | b == True =
    let (newn, newlty) = alphaConvTypes lty ctx n
     in (newn, WF True x newlty)
  | otherwise =
    let newT = "_T" ++ show n
        (newn, newlty) = alphaConvTypes lty (Map.insert x newT ctx) (n + 1)
     in (newn, WF b x newlty)
alphaConvTypes x _ n = (n, x)

termListToEquaList :: [LTerm] -> LType -> Int -> Map String LType -> (Int, [LTypeEqua])
termListToEquaList (x : xs) lty n ctx =
  let (newN1, lteqs1) = genEquas x lty n ctx
      (newN2, lteqs2) = termListToEquaList xs lty newN1 ctx
   in (newN2, lteqs1 ++ lteqs2)
termListToEquaList [] _ n _ = (n, [])

genEquas :: LTerm -> LType -> Int -> Map String LType -> (Int, [LTypeEqua])
genEquas (Var x) lty n context =
  case (Map.lookup x context) of
    Just ltyv -> (n, (LTypeEqua lty ltyv) : [])
    Nothing -> error "in genEquas 1"
genEquas (Abs v bodyLTe) lty n context =
  let ltya = TVar ("T" ++ show n)
   in let ltyr = TVar ("T" ++ show (n + 1))
       in let newContext = Map.insert v ltya context
           in let (newN, newLTyEqs) = genEquas bodyLTe ltyr (n + 2) newContext
               in (newN, (LTypeEqua lty (TArrow ltya ltyr)) : newLTyEqs)
genEquas (App Fix (Abs v body)) lty n context =
  let tfix = TVar ("T" ++ show n)
      (newN, newEqs) = genEquas body tfix (n + 1) (Map.insert v tfix context)
   in (newN, (LTypeEqua lty tfix) : newEqs)
genEquas (App lte1 lte2) lty n context =
  let ltya = TVar ("T" ++ show n)
      (newN1, newLTyEquas1) = genEquas lte1 (TArrow ltya lty) (n + 1) context
      (newN2, newLTyEquas2) = genEquas lte2 (ltya) newN1 context
   in (newN2, newLTyEquas1 ++ newLTyEquas2)
genEquas (LInt _) lty n _ =
  (n, (LTypeEqua lty TInt) : [])
genEquas (List l) lty n ctx =
  let newTV = (TVar ("T" ++ show n))
      newEqua = LTypeEqua lty (TList newTV)
      (newN, lteqs) = termListToEquaList l newTV (n + 1) ctx
   in (newN, newEqua : lteqs)
genEquas (IfZ lte1 lte2 lte3) lty n context =
  let newT = TVar ("T" ++ show n)
   in let (newN1, newEqs1) = genEquas lte1 TInt (n + 1) context
       in let (newN2, newEqs2) = genEquas lte2 newT newN1 context
           in let (newN3, newEqs3) = genEquas lte3 newT newN2 context
               in (newN3, (LTypeEqua lty newT) : (newEqs1 ++ newEqs2 ++ newEqs3))
genEquas (IfE lte1 lte2 lte3) lty n context =
  let newTa = TVar ("T" ++ show n)
   in let newTn = TVar ("T" ++ show (n + 1))
       in let (newN1, newEqs1) = genEquas lte1 (TList newTa) (n + 2) context
           in let (newN2, newEqs2) = genEquas lte2 newTn newN1 context
               in let (newN3, newEqs3) = genEquas lte3 newTn newN2 context
                   in (newN3, (LTypeEqua lty newTn) : (newEqs1 ++ newEqs2 ++ newEqs3))
genEquas (Let v lte1 lte2) lty n context =
  case (typeDetection lte1) of
    TypeDetectionSuccess _ _ newLTy ->
      case (isNonExpansible lte1) of
        True ->
          let newContext = Map.insert v (generalise context newLTy) context
           in genEquas lte2 lty n newContext
        False ->
          let newContext = Map.insert v (weakGeneralise context newLTy) context
           in genEquas lte2 lty n newContext
    TypeDetectionFailure _ _ str -> error ("genEquas failure 1:" ++ str)
genEquas Add lty n _ =
  (n, (LTypeEqua lty (TArrow (TArrow TInt TInt) TInt)) : [])
genEquas Sub lty n _ =
  (n, (LTypeEqua lty (TArrow (TArrow TInt TInt) TInt)) : [])
genEquas Cons lty n _ =
  let newV = "T" ++ show n
      newT = TVar newV
   in (n + 1, (LTypeEqua (TPoly newV (TArrow (TArrow newT (TList newT)) (TList newT))) lty) : [])
genEquas Hd lty n _ =
  let newV = "T" ++ show n
      newT = TVar newV
   in (n + 1, LTypeEqua (TPoly newV (TArrow (TList newT) newT)) lty : [])
genEquas Tl lty n _ =
  let newV = "T" ++ show n
      newT = TVar newV
   in (n + 1, LTypeEqua (TPoly newV (TArrow (TList newT) (TList newT))) lty : [])
genEquas Ref lty n _ =
  let newV = "T" ++ show n
      newT = TPoly newV (TArrow (TVar newV) (TRef (TVar newV)))
   in (n + 1, (LTypeEqua lty newT) : [])
genEquas Deref lty n _ =
  let newV = "T" ++ show n
      newT = TPoly newV (TArrow (TRef (TVar newV)) (TVar newV))
   in (n + 1, (LTypeEqua lty newT) : [])
genEquas Assign lty n _ =
  let newV = "T" ++ show n
      newT = TPoly newV (TArrow (TRef (TVar newV)) (TArrow (TVar newV) TUnit))
   in (n + 1, (LTypeEqua lty newT) : [])
genEquas _ _ _ _ = error "genEquas"

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
isNonExpansible (App x y) =
  isNonExpansible x && isNonExpansible y
isNonExpansible (IfZ _ y z) =
  isNonExpansible y && isNonExpansible z
isNonExpansible (IfE _ y z) =
  isNonExpansible y && isNonExpansible z
isNonExpansible _ = False

getFreeVars :: [String] -> LType -> [String]
getFreeVars context (TVar x) =
  if (List.elem x context)
    then []
    else x : []
getFreeVars context (TArrow x y) =
  (getFreeVars context x) ++ (getFreeVars context y)
getFreeVars context (TList t) =
  getFreeVars context t
getFreeVars context (TPoly _ t) =
  getFreeVars context t
getFreeVars context (TRef v) =
  getFreeVars context v
getFreeVars context (WV True _ lty) =
  getFreeVars context lty
getFreeVars context (WF b str lty)
  | b == True = getFreeVars context lty
  | otherwise = getFreeVars (str : context) lty
getFreeVars _ _ = []

generalise :: Map String LType -> LType -> LType
generalise context t =
  let fvs = getFreeVars (Map.keys context) t
   in List.foldr (\x y -> TPoly x y) t fvs

weakGeneralise :: Map String LType -> LType -> LType
weakGeneralise context t =
  let fvs = getFreeVars (Map.keys context) t
   in List.foldr (\x y -> WF False x y) t fvs

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
subs x newLTy (WV True _ lty) =
  subs x newLTy lty
subs x newLTy (WF _ _ lty) =
  subs x newLTy lty
subs _ _ x = x

subsInLTyEq :: String -> LType -> LTypeEqua -> LTypeEqua
subsInLTyEq x newLTy (LTypeEqua lty1 lty2) =
  LTypeEqua (subs x newLTy lty1) (subs x newLTy lty2)

tarrowIsCorrect :: LType -> Bool
tarrowIsCorrect (TArrow (TArrow _ _) _) = False
tarrowIsCorrect (TArrow _ (TArrow x y)) = tarrowIsCorrect (TArrow x y)
tarrowIsCorrect _ = True

tarrowToList :: LType -> [LType]
tarrowToList (TArrow x y) = (tarrowToList x) ++ (tarrowToList y)
tarrowToList x = x : []

tarrowFromList :: [LType] -> LType
tarrowFromList (x : y : []) = TArrow x y
tarrowFromList (x : xs) = TArrow x (tarrowFromList xs)
tarrowFromList [] = error "tarrowFromList"

tarrowUnification :: LType -> LType -> [LTypeEqua]
tarrowUnification (TArrow x1 y1) (TArrow x2 y2) =
  (LTypeEqua x1 x2) : (tarrowUnification y1 y2)
tarrowUnification (TArrow x1 y1) x2 =
  (LTypeEqua (TArrow x1 y1) x2) : []
tarrowUnification x1 (TArrow x2 y2) =
  (LTypeEqua x1) (TArrow x2 y2) : []
tarrowUnification x y =
  (LTypeEqua x y) : []

data UnifStepRes
  = UnifStepSuccess [LTypeEqua]
  | UnifStepFailure String
  deriving (Show)

unificationStep :: [LTypeEqua] -> LType -> Int -> UnifStepRes
unificationStep ((LTypeEqua (TArrow ltya1 ltyb1) (TArrow ltya2 ltyb2)) : tl2) ltyf n
  | (TArrow ltya1 ltyb1) == (TArrow ltya2 ltyb2) = unificationStep tl2 ltyf n
  | otherwise =
    case (tarrowIsCorrect (TArrow ltya1 ltyb1), tarrowIsCorrect (TArrow ltya2 ltyb2)) of
      (True, True) ->
        UnifStepSuccess ((tarrowUnification (TArrow ltya1 ltyb1) (TArrow ltya2 ltyb2)) ++ tl2)
      (True, False) ->
        let newTArr2 = tarrowFromList $ tarrowToList (TArrow ltya2 ltyb2)
         in UnifStepSuccess ((tarrowUnification (TArrow ltya1 ltyb1) newTArr2) ++ tl2)
      (False, True) ->
        let newTArr1 = tarrowFromList $ tarrowToList (TArrow ltya1 ltyb1)
         in UnifStepSuccess ((tarrowUnification newTArr1 (TArrow ltya2 ltyb2)) ++ tl2)
      (False, False) ->
        let newTArr1 = tarrowFromList $ tarrowToList (TArrow ltya1 ltyb1)
            newTArr2 = tarrowFromList $ tarrowToList (TArrow ltya2 ltyb2)
         in UnifStepSuccess ((tarrowUnification newTArr1 newTArr2) ++ tl2)
unificationStep ((LTypeEqua (TVar x) td) : tl2) ltyf _
  | occurCheck2 ltyf (TVar x) || occurCheck2 ltyf td = UnifStepSuccess (tl2 ++ (LTypeEqua (TVar x) td) : [])
  | TVar x == td = UnifStepSuccess tl2
  | occurCheck2 (TVar x) td = UnifStepFailure ((show x) ++ " occurs in " ++ show td)
  | otherwise = UnifStepSuccess (List.map (subsInLTyEq x td) tl2)
unificationStep ((LTypeEqua tg (TVar x)) : tl2) ltyf _
  | occurCheck2 ltyf tg || occurCheck2 ltyf (TVar x) = UnifStepSuccess (tl2 ++ (LTypeEqua tg (TVar x)) : [])
  | TVar x == tg = UnifStepSuccess tl2
  | occurCheck2 (TVar x) tg = UnifStepFailure ((show x) ++ " occurs in " ++ show tg)
  | otherwise = UnifStepSuccess (List.map (subsInLTyEq x tg) tl2)
unificationStep ((LTypeEqua (TPoly v lty) td) : tl2) _ n
  | (TPoly v lty) == td = UnifStepSuccess tl2
  | otherwise =
    let (_, newlty) = alphaConvTypes lty (Map.fromList []) n
     in UnifStepSuccess ((LTypeEqua newlty td) : tl2)
unificationStep ((LTypeEqua tg (TPoly v lty)) : tl2) _ n
  | (TPoly v lty) == tg = UnifStepSuccess tl2
  | otherwise =
    let (_, newlty) = alphaConvTypes lty (Map.fromList []) n
     in UnifStepSuccess ((LTypeEqua tg newlty) : tl2)
unificationStep ((LTypeEqua (TList lty1) (TList lty2)) : tl2) _ _
  | lty1 == lty2 = UnifStepSuccess tl2
  | otherwise = UnifStepSuccess ((LTypeEqua lty1 lty2) : tl2)
unificationStep ((LTypeEqua (WF b v lty) td) : tl2) _ _
  | (WF b v lty) == td = UnifStepSuccess tl2
  | otherwise = UnifStepSuccess ((LTypeEqua lty td) : tl2)
unificationStep ((LTypeEqua tg (WF b v lty)) : tl2) _ _
  | (WF b v lty) == tg = UnifStepSuccess tl2
  | otherwise = UnifStepSuccess ((LTypeEqua lty tg) : tl2)
unificationStep ((LTypeEqua (WV b v lty) td) : tl2) _ _
  | (WF b v lty) == td = UnifStepSuccess tl2
  | occurCheck2 (TVar v) td = UnifStepFailure ("WV : " ++ show v ++ " occurs in " ++ show td)
  | b == True = UnifStepSuccess ((LTypeEqua lty td) : tl2)
  | otherwise = UnifStepSuccess ((LTypeEqua (WV True v td) td) : tl2)
unificationStep ((LTypeEqua tg (WV b v lty)) : tl2) _ _
  | (WF b v lty) == tg = UnifStepSuccess tl2
  | occurCheck2 (TVar v) tg = UnifStepFailure ("WV : " ++ show v ++ " occurs in " ++ show tg)
  | b == True =
    UnifStepSuccess ((LTypeEqua tg lty) : tl2)
  | otherwise =
    UnifStepSuccess ((LTypeEqua tg (WV True v tg)) : tl2)
unificationStep ((LTypeEqua (TRef lty1) (TRef lty2)) : tl2) _ _
  | lty1 == lty2 = UnifStepSuccess tl2
  | otherwise = UnifStepSuccess ((LTypeEqua lty1 lty2) : tl2)
unificationStep ((LTypeEqua x y) : l) _ _
  | x == y = UnifStepSuccess l
  | otherwise = UnifStepFailure ((show x) ++ " is incompatible with " ++ show y)
unificationStep [] _ _ = UnifStepFailure "Empty list"

showEqL :: [LTypeEqua] -> String
showEqL l = List.foldr (++) " " (List.map show l)

show2EqLs :: ([LTypeEqua], [LTypeEqua]) -> String
show2EqLs (l1, l2) = showEqL l1 ++ "\n ### \n" ++ showEqL l2

data UnificationRes
  = UnifSuccess [String] LTypeEqua
  | UnifFailure [String] String
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
isSimplifiable (LTypeEqua (WF _ _ _) _) = True
isSimplifiable (LTypeEqua _ (WF _ _ _)) = True
isSimplifiable (LTypeEqua (WV _ _ _) _) = True
isSimplifiable (LTypeEqua _ (WV _ _ _)) = True
isSimplifiable (LTypeEqua (TPoly _ _) _) = True
isSimplifiable (LTypeEqua _ (TPoly _ _)) = True
isSimplifiable _ = False

unifyEqs :: [LTypeEqua] -> [String] -> LType -> Int -> UnificationRes
unifyEqs (x : []) strl lty n
  | isSimplifiable x =
    case (unificationStep (x : []) lty n) of
      UnifStepSuccess newl ->
        unifyEqs newl ((show newl) : strl) lty n
      UnifStepFailure msg -> UnifFailure strl ("Unification failure (unifyEqs) : " ++ msg)
  | otherwise = UnifSuccess strl x
unifyEqs l strl lty n =
  case (unificationStep l lty n) of
    UnifStepSuccess newl ->
      unifyEqs newl ((show newl) : strl) lty n
    UnifStepFailure msg -> UnifFailure strl ("Unification failure (unifyEqs) : " ++ msg)

getType :: LTypeEqua -> LType -> LType
getType (LTypeEqua x y) lty
  | x == lty = y
  | y == lty = x
  | otherwise = error (show lty ++ " not present in " ++ show (LTypeEqua x y))

data TypeDetectionRes
  = TypeDetectionSuccess [String] LTerm LType
  | TypeDetectionFailure [String] LTerm String

instance Show TypeDetectionRes where
  show (TypeDetectionSuccess l lte lty) =
    "Type inference of : " ++ show lte ++ "\n\n"
      ++ (List.intercalate "\n" l)
      ++ "\n\n"
      ++ "Type inference of : "
      ++ show lte
      ++ " resulted in : "
      ++ show lty
      ++ "\n"
  show (TypeDetectionFailure l lte msg) =
    "Type inference of : " ++ show lte ++ "\n\n"
      ++ (List.intercalate "\n" l)
      ++ "\n\n"
      ++ "Type inference of : "
      ++ show lte
      ++ " failed : "
      ++ msg

--isInEq :: LType -> LTypeEqua -> Bool
--isInEq lty (LTypeEqua lty1 lty2) = occurCheck2 lty lty1 || occurCheck2 lty lty2

--getTypeInEq :: LType -> LTypeEqua -> LType
--getTypeInEq lty (LTypeEqua lty1 lty2)
--  | occurCheck2 lty lty1 = lty1
--  | occurCheck2 lty lty2 = lty2

typeDetection :: LTerm -> TypeDetectionRes
typeDetection lte =
  let lty = TVar "T0"
   in let (n, eqs) = (genEquas lte lty 1 (Map.fromList []))
       in case (unifyEqs eqs ((show eqs) : []) lty n) of
            UnifSuccess strl resEq -> TypeDetectionSuccess (List.reverse strl) lte (getType resEq lty)
            UnifFailure strl msg -> TypeDetectionFailure (List.reverse strl) lte msg
