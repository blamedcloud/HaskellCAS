module Types where

infixl 4 :+:
infixl 5 :*:, :/:
infixr 6 :^:

type Variable = Char

--to Extend:
--  1. Add new Types to Expr
--  2. Add new simplification rules to Simplify
--  3. Add new patterns to:
--      a. negate'  --if needed
--      b. mapVar
--      c. evalExpr
--  4. Write corresponding derivative rules

data Expr a = Var Variable
            | Const a
            | (Expr a) :+: (Expr a)
            | (Expr a) :*: (Expr a)
            | (Expr a) :^: (Expr a)
            | (Expr a) :/: (Expr a)
            | Ln (Expr a)
            | Sin (Expr a)
            | Cos (Expr a)
            | Tan (Expr a)
            | Sec (Expr a)
            | Csc (Expr a)
            | Cot (Expr a)
            | Infinity
            | NegInfinity
            | IndForm
            | Undefined
            deriving (Show, Eq)
