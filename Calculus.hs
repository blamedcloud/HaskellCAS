module Calculus where

import Types
import Simplify
import Eval

derivativeWRT :: (Num a) => Variable -> Expr a -> Expr a
derivativeWRT x (Var y)
    | x == y                      = Const 1
    | otherwise                   = Const 0
derivativeWRT x (Const c)         = Const 0
-- product rule (ab' + a'b)
derivativeWRT x (a :*: b)         = a :*: (derivativeWRT x b) :+: (derivativeWRT x a) :*: b
-- power rule (n * a^(n-1) * a') 
derivativeWRT x (a :^: (Const c)) = Const c :*: (a :^: (Const $ c-1)) :*: (derivativeWRT x a)
--power rule for rational exponents:
derivativeWRT x (a :^: (Const n :/: Const d)) = (Const n :/: Const d) 
                                                :*:
                                                (a :^: ((Const n :+: (negate' (Const d))) :/: Const d))
                                                :*:
                                                (derivativeWRT x a)
derivativeWRT x (a :+: b)         = (derivativeWRT x a) :+: (derivativeWRT x b)
-- quotient rule ( (a'b - b'a) / b^2 )
derivativeWRT x (a :/: b)         = (((derivativeWRT x a) :*: b) :+: (negate' ((derivativeWRT x b) :*: a)))
                                    :/:
                                    (b :^: (Const 2))
--Special derivatives implicitly include chain rule
derivativeWRT x (Ln a)            = ((Const 1) :/: a) :*: (derivativeWRT x a)
derivativeWRT x (Sin a)           = (Cos a) :*: (derivativeWRT x a)
derivativeWRT x (Cos a)           = (negate' (Sin a)) :*: (derivativeWRT x a)
derivativeWRT x (Tan a)           = ((Sec a) :^: (Const 2)) :*: (derivativeWRT x a)
derivativeWRT x (Sec a)           = (Sec a) :*: (Tan a) :*: (derivativeWRT x a)
derivativeWRT x (Csc a)           = (negate' (Csc a)) :*: (Cot a) :*: (derivativeWRT x a)
derivativeWRT x (Cot a)           = (negate' ((Csc a) :^: (Const 2))) :*: (derivativeWRT x a)

-- logarithmic derivative rule: ( f  = g^h )
--                              ( f' = g^h*h'*ln(g) + g^(h-1)*h*g' )
derivativeWRT x f@(g :^: h) = f :*: h' :*: Ln (g) :+: (g :^: (h :+: Const (-1))) :*: h :*: g' 
    where h' = derivativeWRT x h
          g' = derivativeWRT x g

derivativeWRT x otherExpr         = error "Derivative rule not implemented... Sorry"
-- add more derivative rules ... (like x^x)


ddWRT :: (Ord a, Num a, Eq a, Floating a) => Variable -> Expr a -> Expr a
ddWRT x = fullSimplify . derivativeWRT x

ddx :: (Ord a, Num a, Eq a, Floating a) => Expr a -> Expr a
ddx = ddWRT 'x'

ddWRTs :: (Ord a, Num a, Eq a, Floating a) => Variable -> Expr a -> [Expr a]
ddWRTs x = iterate $ ddWRT x

ddxs :: (Ord a, Num a, Eq a, Floating a) => Expr a -> [Expr a]
ddxs = iterate ddx

nthDerivativeWRT :: (Ord a, Num a, Eq a, Floating a) => Variable -> Int -> Expr a -> Expr a
nthDerivativeWRT x n = foldr1 (.) (replicate n (ddWRT x))

nthDerivative :: (Ord a, Num a, Eq a, Floating a) => Int -> Expr a -> Expr a
nthDerivative n = foldr1 (.) (replicate n ddx)

--assumes the Expr it is given is a function of a single variable
taylor :: (Ord a, Num a, Eq a, Floating a) => Expr a -> [Expr a]
taylor expr = fmap fullSimplify (fmap series exprs)
    where indices = fmap fromIntegral [1..]
          derivs = ddWRTs 'a' (changeVars 'a' expr)
            where changeVars c = mapVar (\_ -> Var c)
          facts   = fmap Const $ scanl1 (*) ((fromIntegral 1):indices)
          exprs   = zip (zipWith (:/:) derivs facts) ((fromIntegral 0):indices) -- f^(n)(x) / n!
          series (expr, n) =
            expr :*: ((Var 'x' :+: (negate' $ Var 'a')) :^: Const n) -- f^(n)(a)/n! * (x-a)^n


maclaurin :: (Ord a, Num a, Eq a, Floating a) => Expr a -> [Expr a]
maclaurin = fmap (plugIn 'a' 0) . taylor

nthTaylor :: (Ord a, Num a, Eq a, Floating a) => Int -> Expr a -> Expr a
nthTaylor n expr = fullSimplify $ foldl1 (:+:) (take n $ taylor expr)

nthTaylorAt :: (Ord a, Num a, Eq a, Floating a) => Int -> a -> Expr a -> Expr a
nthTaylorAt n a expr = fullSimplify $ plugIn 'a' a (nthTaylor n expr)

nthMaclaurin :: (Ord a, Num a, Eq a, Floating a) => Int -> Expr a -> Expr a
nthMaclaurin n expr = fullSimplify $ sumExpr (take n $ maclaurin expr)

sumExpr :: (Num a) => [Expr a] -> Expr a
sumExpr []  = Const 0
sumExpr [a] = a
sumExpr (a:as) = a :+: sumExpr as

evalTaylorWithPrecision :: (Ord a, Num a, Eq a, Floating a) => a -> a -> Int -> Expr a -> a
evalTaylorWithPrecision a x prec  =
    sum . map (evalExpr' . plugIn 'x' x . plugIn 'a' a) . take prec . taylor 
    
defaultPrecision :: Int
defaultPrecision = 100

evalTaylor :: (Ord a, Num a, Eq a, Floating a) => a -> a -> Expr a -> a
evalTaylor a x = evalTaylorWithPrecision a x defaultPrecision

evalMaclaurin :: (Ord a, Num a, Eq a, Floating a) => a -> Expr a -> a
evalMaclaurin = evalTaylor 0

evalMaclaurinWithPrecision :: (Ord a, Num a, Eq a, Floating a) => a -> Int -> Expr a -> a
evalMaclaurinWithPrecision = evalTaylorWithPrecision 0





