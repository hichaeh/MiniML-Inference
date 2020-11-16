module Types where

--import Data.List as List
--import Data.Map as Map
--import Terms

data LType
  = TVar String
  | TArrow LType LType
  | TList LType
  | TPoly String LType
  | TRef LType
  | TInt
  | TUnit
  | WVT LType --  | WV Bool String LType
  | WVF String
  | WF Bool String LType
  deriving (Eq)

instance Show LType where
  show (TVar v) = v
  show (TArrow srct destt) = "( " ++ show srct ++ " -> " ++ show destt ++ " )"
  show (TList x) = "[" ++ show x ++ "]"
  show (TPoly x y) = "∀" ++ x ++ "." ++ show y
  show (TRef x) = "Ref ( " ++ show x ++ " )"
  show TInt = "ℕ"
  show TUnit = "⬤"
  show (WVT lty) = show lty
  show (WVF str) = str
  show (WF True _ lty) = show lty
  show (WF False str lty) = "∀" ++ str ++ "." ++ show lty

data LTypeEqua = LTypeEqua LType LType deriving (Eq)

instance Show LTypeEqua where
  show (LTypeEqua lty1 lty2) = show lty1 ++ " = " ++ show lty2
