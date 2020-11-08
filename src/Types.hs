module Types where

import Data.Map as Map
import Data.List as List
import Terms

data LType = TVar String
  | TArrow LType LType 
  | TInt
  | TList LType
  | TPoly String LType deriving Eq

instance Show LType where 
  show (TVar v) = v
  show (TArrow srct destt) = (show srct) ++ " -> " ++ (show destt)
  show TInt = "ℕ"
  show (TList x) =  "[" ++ (show x) ++ "]"
  show (TPoly x y) =  "∀" ++ x ++ "." ++ show y

data LTypeEqua = LTypeEqua LType LType deriving Eq

instance Show LTypeEqua where
  show (LTypeEqua lty1 lty2) = (show lty1) ++ " = " ++ (show lty2)

occurCheck :: String -> LType -> Bool
occurCheck v (TVar x) = v == x
occurCheck v (TArrow lty1 lty2) = occurCheck v lty1 || occurCheck v lty2
occurCheck _ TInt = False
occurCheck v (TList ltype) = occurCheck v ltype
occurCheck v (TPoly _ ltype) = occurCheck v ltype

genEquas :: LTerm -> LType -> Int -> Map String LType -> (Int, [LTypeEqua])
genEquas (Var x) lty n context =
  case (Map.lookup x context) of
    Just ltyv -> (n, (LTypeEqua lty ltyv):[])
    Nothing -> error "in genEquas 1"

genEquas (Abs v bodyLTe) lty n context =
  let ltya = TVar ("T" ++ show n) in
  let ltyr = TVar ("T" ++ show (n+1)) in
  let newContext = Map.insert v ltya context in 
  let (newN, newLTyEqs) =  genEquas bodyLTe ltyr (n+2) newContext in
    (newN, (LTypeEqua lty (TArrow ltya ltyr)):newLTyEqs)

genEquas (App Fix (Abs v body)) lty n context =
  let tfix = TVar ("T" ++ show n)
      (newN, newEqs) = genEquas body tfix (n+1) (Map.insert v tfix context)
  in
    (newN, (LTypeEqua lty tfix):newEqs)

genEquas (App lte1 lte2) lty n context =
  let ltya = TVar ("T" ++ show n) 
      (newN1, newLTyEquas1) = genEquas lte1 (TArrow ltya lty) (n+1) context
      (newN2, newLTyEquas2) = genEquas lte2 (ltya) newN1 context
  in
    (newN2, newLTyEquas1 ++ newLTyEquas2)

genEquas (LInt _) lty n _ =
  (n, (LTypeEqua TInt lty):[])

genEquas (Let v lte1 lte2) lty n context = 
  case (typeDetection lte1) of 
    TypeDetectionSuccess _ newLTy ->
 --      if (isNonExpansible lte1)
 --        then 
          let newContext = Map.insert v (generalise context newLTy) context in
            genEquas lte2 lty n newContext
 --        else  
 --          undefined
    TypeDetectionFailure _ str -> error ("genEquas failure 1:" ++ str)

genEquas (IfZ lte1 lte2 lte3) lty n context =
  let newT = TVar ("T" ++ show n) in
  let (newN1, newEqs1) = genEquas lte1 TInt (n+1) context in
  let (newN2, newEqs2) = genEquas lte2 newT newN1 context in
  let (newN3, newEqs3) = genEquas lte3 newT newN2 context in
    (newN3, (LTypeEqua lty newT):( newEqs1 ++ newEqs2 ++ newEqs3))
genEquas (IfE lte1 lte2 lte3) lty n context =
  let newTa = TVar ("T" ++ show n) in
  let newTn = TVar ("T" ++ show (n+1)) in
  let (newN1, newEqs1) = genEquas lte1 (TList newTa) (n+2) context in
  let (newN2, newEqs2) = genEquas lte2 newTn newN1 context in
  let (newN3, newEqs3) = genEquas lte3 newTn newN2 context in
    (newN3, (LTypeEqua lty newTn):(newEqs1 ++ newEqs2 ++ newEqs3))

genEquas Add lty n _ =
  (n, (LTypeEqua lty (TArrow (TArrow TInt TInt) TInt)):[])
genEquas Sub lty n _ =
  (n, (LTypeEqua lty (TArrow (TArrow TInt TInt) TInt)):[])
genEquas Cons lty n _ =
  let newT = TVar ("T" ++ show n) in
    (n+1, (LTypeEqua ( TPoly ("T" ++ show n) (TArrow (TArrow newT (TList newT)) (TList newT) )) lty):[])
genEquas Hd lty n _ =
  let newT = TVar ("T" ++ show n) in
    (n+1, LTypeEqua (TPoly ("T" ++ show n) (TArrow (TList newT) newT)) lty:[])
genEquas Tl lty n _ =
  let newT = TVar ("T" ++ show n) in
    (n+1, LTypeEqua (TPoly ("T" ++ show n) (TArrow (TList newT) (TList newT))) lty:[])

-- genEquas Fix lty n _ = 

genEquas _ _ _ _ = error "genEquas"

-- ?????
isNonExpansible :: LTerm -> Bool
isNonExpansible (LInt _) = True
isNonExpansible (Abs _ _ ) = True

isNonExpansible (Let _ val body) = 
  isNonExpansible val && isNonExpansible body

isNonExpansible (App Fix l) =
  isNonExpansible l

isNonExpansible (App x y) =
  isNonExpansible x && isNonExpansible y

isNonExpansible (IfZ x y z) =
  isNonExpansible x && isNonExpansible y && isNonExpansible z
isNonExpansible (IfE x y z) =
  isNonExpansible x && isNonExpansible y && isNonExpansible z

isNonExpansible _ =  False



getFreeVars :: Map String LType -> LType -> [String] 
getFreeVars context (TVar x) =
  if (Map.member x context) then [] 
  else x:[]
getFreeVars context (TArrow x y) =
  (getFreeVars context x) ++ (getFreeVars context y)
getFreeVars context (TList t) = 
  getFreeVars context t
getFreeVars context (TPoly _ t) = 
  getFreeVars context t
getFreeVars _ _ = []

generalise :: Map String LType -> LType -> LType
generalise context t = 
  let fvs = getFreeVars context t in
    List.foldr (\x y -> TPoly x y) t fvs

subs :: String -> LType -> LType -> LType
subs x newLTy (TVar y) 
  | x == y = newLTy
  | otherwise = TVar y

subs x newLTy (TArrow lte1 lte2) =
  TArrow (subs x newLTy lte1) (subs x newLTy lte2)

subs x newLTy (TList lte) =
  TList (subs x newLTy lte)

subs x newLTy (TPoly v lte) =
  TPoly v (subs x newLTy lte)

subs _ _ TInt = TInt

subsInLTyEq :: String -> LType -> LTypeEqua -> LTypeEqua
subsInLTyEq x newLTy (LTypeEqua lty1 lty2) =
  LTypeEqua (subs x newLTy lty1) (subs x newLTy lty2)



tarrowIsCorrect :: LType -> Bool
tarrowIsCorrect (TArrow (TArrow _ _) _) = False
tarrowIsCorrect (TArrow _ (TArrow x y)) = tarrowIsCorrect (TArrow x y) 
tarrowIsCorrect _ = True

tarrowToList :: LType -> [LType]
tarrowToList (TArrow x y) = (tarrowToList x) ++ (tarrowToList y)
tarrowToList x = x:[]

tarrowFromList :: [LType] -> LType
tarrowFromList (x:y:[]) = TArrow x y
tarrowFromList (x:xs) = TArrow x (tarrowFromList xs)
tarrowFromList [] = error "tarrowFromList"

tarrowUnification :: LType -> LType -> [LTypeEqua]
tarrowUnification (TArrow x1 y1) (TArrow x2 y2) =
  (LTypeEqua x1 x2):(tarrowUnification y1 y2)

tarrowUnification (TArrow x1 y1) x2 =
  (LTypeEqua (TArrow x1 y1) x2):[]

tarrowUnification x1 (TArrow x2 y2)=
  (LTypeEqua x1) (TArrow x2 y2):[]

tarrowUnification x y = 
  (LTypeEqua x y):[]

data UnifStepRes = 
    UnifStepSuccess [LTypeEqua] 
  | UnifOver LTypeEqua 
  | UnifStepFailure String

unificationStep :: [LTypeEqua] -> LType -> UnifStepRes

unificationStep ((LTypeEqua (TArrow x y) TInt):[]) _ = 
  UnifStepFailure ("Incompatible types : " ++ show (TArrow x y) 
                                ++ " and " ++ show TInt)
unificationStep ((LTypeEqua TInt (TArrow x y )):[]) _ = undefined
  UnifStepFailure ("Incompatible types : " ++ show TInt 
                                ++ " and " ++ show (TArrow x y))
unificationStep ((LTypeEqua (TArrow x y) (TList z)):[]) _ = undefined
  UnifStepFailure ("Incompatible types : " ++ show (TArrow x y) 
                                ++ " and " ++ show (TList z) )
unificationStep ((LTypeEqua (TList z) (TArrow x y)):[]) _ = undefined
  UnifStepFailure ("Incompatible types : " ++ show (TList z) 
                                ++ " and " ++ show (TArrow x y))
unificationStep ((LTypeEqua TInt (TList z)):[]) _ = undefined
  UnifStepFailure ("Incompatible types : " ++ show TInt 
                                ++ " and " ++ show (TList z) )
unificationStep ((LTypeEqua (TList z) TInt):[]) _ = undefined
  UnifStepFailure ("Incompatible types : " ++ show (TList z) 
                                ++ " and " ++ show TInt)


unificationStep ((LTypeEqua (TArrow ltya1 ltyb1) (TArrow ltya2 ltyb2)):[]) _
  | (TArrow ltya1 ltyb1) == (TArrow ltya2 ltyb2) = UnifStepFailure "EmpTY LisT 1"
  | otherwise =
    case (tarrowIsCorrect (TArrow ltya1 ltyb1), tarrowIsCorrect (TArrow ltya2 ltyb2)) of
      (True, True) ->
        UnifStepSuccess ((tarrowUnification (TArrow ltya1 ltyb1) (TArrow ltya2 ltyb2)) ++ [])
      (True, False) ->
        let newTArr2 = tarrowFromList $ tarrowToList (TArrow ltya2 ltyb2) in
          UnifStepSuccess ((tarrowUnification (TArrow ltya1 ltyb1) newTArr2) ++ [])
      (False, True) ->
        let newTArr1 = tarrowFromList $ tarrowToList (TArrow ltya1 ltyb1) in
          UnifStepSuccess ((tarrowUnification newTArr1 (TArrow ltya2 ltyb2)) ++ [])
      (False, False) ->
        let newTArr1 = tarrowFromList $ tarrowToList (TArrow ltya1 ltyb1) 
            newTArr2 = tarrowFromList $ tarrowToList (TArrow ltya2 ltyb2)in
          UnifStepSuccess ((tarrowUnification newTArr1 newTArr2) ++ [])

unificationStep ((LTypeEqua (TArrow ltya1 ltyb1) (TArrow ltya2 ltyb2)):tl2) ltyf
  | (TArrow ltya1 ltyb1) == (TArrow ltya2 ltyb2) = unificationStep tl2 ltyf
  | otherwise =
    case (tarrowIsCorrect (TArrow ltya1 ltyb1), tarrowIsCorrect (TArrow ltya2 ltyb2)) of
      (True, True) ->
        UnifStepSuccess ((tarrowUnification (TArrow ltya1 ltyb1) (TArrow ltya2 ltyb2)) ++ tl2)
      (True, False) ->
        let newTArr2 = tarrowFromList $ tarrowToList (TArrow ltya2 ltyb2) in
          UnifStepSuccess ((tarrowUnification (TArrow ltya1 ltyb1) newTArr2) ++ tl2)
      (False, True) ->
        let newTArr1 = tarrowFromList $ tarrowToList (TArrow ltya1 ltyb1) in
          UnifStepSuccess ((tarrowUnification newTArr1 (TArrow ltya2 ltyb2)) ++ tl2)
      (False, False) ->
        let newTArr1 = tarrowFromList $ tarrowToList (TArrow ltya1 ltyb1) 
            newTArr2 = tarrowFromList $ tarrowToList (TArrow ltya2 ltyb2)in
          UnifStepSuccess ((tarrowUnification newTArr1 newTArr2) ++ tl2)


unificationStep ((LTypeEqua (TVar x) td):[]) _
  | TVar x == td = UnifStepFailure "EmpTY LisT 2"
  | occurCheck x td = UnifStepFailure ((show x) ++ " occurs in " ++ show td)
  | otherwise = UnifOver (LTypeEqua (TVar x) td)

unificationStep ((LTypeEqua (TVar x) td):tl2) ltyf
  | (TVar x) == ltyf = UnifStepSuccess (tl2 ++ (LTypeEqua (TVar x) td):[]) 
  | td == ltyf = UnifStepSuccess (tl2 ++ (LTypeEqua (TVar x) td):[])
  | TVar x == td = UnifStepSuccess tl2
  | occurCheck x td = UnifStepFailure ((show x) ++ " occurs in " ++ show td)
  | otherwise = UnifStepSuccess (List.map (subsInLTyEq x td) tl2)


unificationStep ((LTypeEqua td (TVar x)):[]) _
  | TVar x == td = UnifStepFailure "EmpTY LisT 3"
  | occurCheck x td = UnifStepFailure ((show x) ++ " occurs in " ++ show td)
  | otherwise =  UnifOver (LTypeEqua td (TVar x))

unificationStep ((LTypeEqua td (TVar x)):tl2) ltyf
  | td == ltyf = UnifStepSuccess (tl2 ++ (LTypeEqua td (TVar x)):[])
  | TVar x == td = UnifStepSuccess tl2
  | occurCheck x td = UnifStepFailure ((show x) ++ " occurs in " ++ show td)
  | otherwise = UnifStepSuccess (List.map (subsInLTyEq x td) tl2)


unificationStep ((LTypeEqua (TPoly v lty) td):[]) _
  | (TPoly v lty) == td = UnifStepFailure "EmpTY LisT 4"
  | otherwise = UnifOver (LTypeEqua (TPoly v lty) td)

unificationStep ((LTypeEqua (TPoly v lty) td):tl2) ltyf
  | td == ltyf = UnifStepSuccess (tl2 ++ (LTypeEqua (TPoly v lty) td):[])  
  | (TPoly v lty) == td = UnifStepSuccess tl2
  | otherwise = UnifStepSuccess ((LTypeEqua lty td):tl2)


unificationStep ((LTypeEqua td (TPoly v lty)):[]) _
  | (TPoly v lty) == td = UnifStepFailure "EmpTY LisT 5"
  | otherwise = UnifOver (LTypeEqua td (TPoly v lty))

unificationStep ((LTypeEqua td (TPoly v lty)):tl2) ltyf
  | td == ltyf = UnifStepSuccess (tl2 ++ (LTypeEqua td (TPoly v lty)):[])
  | (TPoly v lty) == td = UnifStepSuccess tl2
  | otherwise = UnifStepSuccess ((LTypeEqua td lty):tl2)


unificationStep ((LTypeEqua (TList lty1) (TList lty2)):[]) _ 
  | lty1 == lty2 = UnifStepFailure "EmpTY LisT 6"
  | otherwise = UnifOver (LTypeEqua lty1 lty2)

unificationStep ((LTypeEqua (TList lty1) (TList lty2)):tl2) _
  | lty1 == lty2 = UnifStepSuccess tl2
  | otherwise = UnifStepSuccess ((LTypeEqua lty1 lty2):tl2)


unificationStep ((LTypeEqua _ _):l) _ =
  UnifStepSuccess (List.reverse l)

unificationStep [] _ = UnifStepFailure "Empty list"

--unificationStep _ _ = UnifStepFailure "Weird ????"


showEqL :: [LTypeEqua] -> String
showEqL l =  List.foldr (++) " " (List.map show l) 

show2EqLs :: ([LTypeEqua], [LTypeEqua]) -> String 
show2EqLs (l1,l2) = showEqL l1 ++ "\n ### \n" ++ showEqL l2


data UnificationRes = 
    UnifSuccess [(String, String)] LTypeEqua 
  | UnifFailure [(String, String)] String

unifyEqsBis :: [LTypeEqua] -> [(String, String)] -> LType -> UnificationRes
unifyEqsBis l strl lty = 
  case (unificationStep l lty) of
    UnifStepSuccess newl -> 
      unifyEqsBis newl ((show l, show newl):strl) lty
    UnifStepFailure msg -> UnifFailure strl ("Unification failure (unifyEqsBis) : " ++ msg)
    UnifOver e -> UnifSuccess strl e 

unifyEqs :: [LTypeEqua] -> LType -> IO ()
unifyEqs l lty = 
  case (unificationStep l lty) of
    UnifStepSuccess newl -> 
      do 
        putStrLn $ show l
        putStrLn $ show newl ++ "\n"
        unifyEqs newl lty
    UnifStepFailure msg -> putStrLn ("Unification failure (unifyEqs) : " ++ msg)
    UnifOver e -> putStrLn ("Unification over: " ++ show e)


getType :: LTypeEqua -> LType -> LType
getType (LTypeEqua x y) lty 
  | x == lty = y
  | y == lty = x
  | otherwise = error (show lty ++ " not present in " ++ show (LTypeEqua x y))

data TypeDetectionRes = 
    TypeDetectionSuccess [(String, String)] LType
  | TypeDetectionFailure [(String, String)] String deriving Show


typeDetection :: LTerm -> TypeDetectionRes
typeDetection lte = 
  let lty = TVar "T0" in
  let (_, eqs) = (genEquas lte lty 1 (Map.fromList []) ) in
    case (unifyEqsBis eqs [] lty) of
      UnifSuccess strl resEq -> TypeDetectionSuccess strl (getType resEq lty)
      UnifFailure strl msg   -> TypeDetectionFailure strl msg


