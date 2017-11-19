module Eval where

import Types
import Simplify

mapVar :: (Variable -> Expr a) -> Expr a -> Expr a
mapVar f (Var d)    = f d
mapVar _ (Const a)  = Const a
mapVar f (a :+: b)  = (mapVar f a) :+: (mapVar f b)
mapVar f (a :*: b)  = (mapVar f a) :*: (mapVar f b)
mapVar f (a :^: b)  = (mapVar f a) :^: (mapVar f b)
mapVar f (a :/: b)  = (mapVar f a) :/: (mapVar f b)
mapVar f (Ln a)     = Ln (mapVar f a)
mapVar f (Sin a)    = Sin (mapVar f a)
mapVar f (Cos a)    = Cos (mapVar f a)
mapVar f (Tan a)    = Tan (mapVar f a)
mapVar f (Csc a)    = Csc (mapVar f a)
mapVar f (Sec a)    = Sec (mapVar f a)
mapVar f (Cot a)    = Cot (mapVar f a)


plugIn :: (Ord a, Num a, Eq a, Floating a) => Variable -> a -> Expr a -> Expr a
plugIn c val = fullSimplify . mapVar (\x -> if x == c then Const val else Var x)

substitute :: (Ord a, Num a, Eq a, Floating a) => Variable -> Expr a -> Expr a -> Expr a
substitute var subExpr = fullSimplify . mapVar (\x -> if x == var then subExpr else Var x)

evalExpr :: (Ord a, Num a, Eq a, Floating a) => Variable -> a -> Expr a -> a
evalExpr c x = evalExpr' . plugIn c x

evalExpr' :: (Num a, Floating a) => Expr a -> a
evalExpr' (Const a) = a
evalExpr' (Var   c) = error $ "Variables (" ++ [c] ++ ") still exist in formula. Try plugging in a value!"
evalExpr' Infinity  = error $ "Infinity"
evalExpr' NegInfinity = error $ "-Infinity"
evalExpr' Undefined = error $ "Undefined"
evalExpr' IndForm   = error $ "Indeterminate Form"
evalExpr' (a :+: b) = (evalExpr' a) + (evalExpr' b)
evalExpr' (a :*: b) = (evalExpr' a) * (evalExpr' b)
evalExpr' (a :^: b) = (evalExpr' a) ** (evalExpr' b)
evalExpr' (a :/: b) = (evalExpr' a) / (evalExpr' b)
evalExpr' (Ln a)    = log (evalExpr' a)
evalExpr' (Sin a)   = sin (evalExpr' a)
evalExpr' (Cos a)   = cos (evalExpr' a)
evalExpr' (Tan a)   = tan (evalExpr' a)
evalExpr' (Sec a)   = sec (evalExpr' a)
    where sec x = 1 / cos x
evalExpr' (Csc a)   = csc (evalExpr' a)
    where csc x = 1 / sin x
evalExpr' (Cot a)   = cot (evalExpr' a)
    where cot x = 1 / tan x
    
                            
negate' :: (Num a) => Expr a -> Expr a
negate' (Const a) = Const (-a)
negate' (a :+: b) = (negate' a) :+: (negate' b)
negate' (a :*: b) = (negate' a) :*: b
negate' (a :/: b) = (negate' a) :/: b
negate' expr      = (Const (-1)) :*: expr --catchall pattern
