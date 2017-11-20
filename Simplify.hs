module Simplify where

import Types

simplify :: (Ord a, Num a, Eq a, Floating a) => Expr a -> Expr a
-- normal simplification rules:
simplify (Const a :+: Const b) = Const (a + b)
simplify (a       :+: Const 0) = simplify a
simplify (Const 0 :+: a      ) = simplify a

simplify (Const a :*: Const b) = Const (a*b)
simplify (a       :*: Const 1) = simplify a
simplify (Const 1 :*: a      ) = simplify a

simplify (Const a :^: Const b)         = Const (a**b)
simplify (a       :^: Const 1)         = simplify a
simplify ((c :^: Const b) :^: Const a) = c :^: (Const (a*b))

simplify ((a :^: Const b) :*: (c :^: Const d))
                                 | a == c = ((simplify a) :^: (Const $ b+d))
simplify ((a :^: b) :*: c)
                                 | a == c = ((simplify a) :^: (simplify (b :+: Const 1)))

simplify (Const a :+: (Const b :+: expr)) = (Const $ a+b) :+: (simplify expr)
simplify (Const a :+: expr :+: Const b)   = (Const $ a+b) :+: (simplify expr)
simplify (expr :+: Const a :+: Const b)   = (Const $ a+b) :+: (simplify expr)

simplify (Const a :*: (Const b :*: expr)) = (Const $ a*b) :*: (simplify expr)
simplify (Const a :*: expr :*: Const b)   = (Const $ a*b) :*: (simplify expr)
simplify (expr :*: Const a :*: Const b)   = (Const $ a*b) :*: (simplify expr)

simplify (Const a :*: (b :+: c))          = (Const a :*: (simplify b)) :+: (Const a :*: (simplify c))

simplify (Const a :/: Const b)
    | a == b && b /= 0   = Const 1 -- only when a == b
simplify (a :/: Const 1) = simplify a

-- write more simplification rules above

-- values at common points (e.g 0,1)
simplify (Ln (Const 0))  = NegInfinity
simplify (Ln (Const 1))  = Const 0
simplify (Sin (Const 0)) = Const 0
simplify (Cos (Const 0)) = Const 1
simplify (Tan (Const 0)) = Const 0
simplify (Sec (Const 0)) = Const 1
simplify (Csc (Const 0)) = Undefined
simplify (Cot (Const 0)) = Undefined

-- special functions at limit points
simplify (Ln (Undefined))    = Undefined
simplify (Ln (IndForm))      = IndForm
simplify (Ln (Infinity))     = Infinity
simplify (Ln (NegInfinity))  = Undefined

simplify (Sin (Undefined))   = Undefined
simplify (Sin (IndForm))     = IndForm
simplify (Sin (Infinity))    = Undefined
simplify (Sin (NegInfinity)) = Undefined

simplify (Cos (Undefined))   = Undefined
simplify (Cos (IndForm))     = IndForm
simplify (Cos (Infinity))    = Undefined
simplify (Cos (NegInfinity)) = Undefined

simplify (Tan (Undefined))   = Undefined
simplify (Tan (IndForm))     = IndForm
simplify (Tan (Infinity))    = Undefined
simplify (Tan (NegInfinity)) = Undefined

simplify (Sec (Undefined))   = Undefined
simplify (Sec (IndForm))     = IndForm
simplify (Sec (Infinity))    = Undefined
simplify (Sec (NegInfinity)) = Undefined

simplify (Csc (Undefined))   = Undefined
simplify (Csc (IndForm))     = IndForm
simplify (Csc (Infinity))    = Undefined
simplify (Csc (NegInfinity)) = Undefined

simplify (Cot (Undefined))   = Undefined
simplify (Cot (IndForm))     = IndForm
simplify (Cot (Infinity))    = Undefined
simplify (Cot (NegInfinity)) = Undefined

-- simplifications involving special results
--  :+:
simplify (Undefined   :+: a)           = Undefined
simplify (a           :+: Undefined)   = Undefined
simplify (IndForm     :+: a)           = IndForm
simplify (a           :+: IndForm)     = IndForm
simplify (Infinity    :+: NegInfinity) = IndForm
simplify (NegInfinity :+: Infinity)    = IndForm
simplify (Infinity    :+: a)           = Infinity
simplify (a           :+: Infinity)    = Infinity
simplify (NegInfinity :+: a)           = NegInfinity
simplify (a           :+: NegInfinity) = NegInfinity
--  :*:
simplify (Undefined   :*: a)           = Undefined
simplify (a           :*: Undefined)   = Undefined
simplify (IndForm     :*: a)           = IndForm
simplify (a           :*: IndForm)     = IndForm
simplify (Infinity    :*: NegInfinity) = NegInfinity
simplify (NegInfinity :*: Infinity)    = NegInfinity
simplify (NegInfinity :*: NegInfinity) = Infinity
simplify (Infinity    :*: (Const a))
                              | a > 0  = Infinity
                              | a < 0  = NegInfinity
                              | a == 0 = IndForm
simplify ((Const a)   :*: Infinity)
                              | a > 0  = Infinity
                              | a < 0  = NegInfinity
                              | a == 0 = IndForm
simplify (NegInfinity :*: (Const a))
                              | a > 0  = NegInfinity
                              | a < 0  = Infinity
                              | a == 0 = IndForm
simplify ((Const a)   :*: NegInfinity)
                              | a > 0  = NegInfinity
                              | a < 0  = Infinity
                              | a == 0 = IndForm
simplify (Infinity    :*: a)           = Infinity
simplify (a           :*: Infinity)    = Infinity
simplify (NegInfinity :*: a)           = NegInfinity
simplify (a           :*: NegInfinity) = NegInfinity
--  :/:
simplify (Undefined   :/: a)           = Undefined
simplify (a           :/: Undefined)   = Undefined
simplify (IndForm     :/: a)           = IndForm
simplify (a           :/: IndForm)     = IndForm
simplify (Infinity    :/: Infinity)    = IndForm
simplify (Infinity    :/: NegInfinity) = IndForm
simplify (NegInfinity :/: Infinity)    = IndForm
simplify (NegInfinity :/: NegInfinity) = IndForm
simplify (a           :/: Infinity)    = Const 0
simplify (a           :/: NegInfinity) = Const 0
simplify (Infinity    :/: a)           = Infinity :*: (Const 1 :/: (simplify a))
simplify (NegInfinity :/: a)           = NegInfinity :*: (Const 1 :/: (simplify a))
-- :^:
simplify (Undefined   :^: a)           = Undefined
simplify (a           :^: Undefined)   = Undefined
simplify (IndForm     :^: a)           = IndForm
simplify (a           :^: IndForm)     = IndForm
simplify (Const 1     :^: Infinity)    = IndForm
simplify (Const 1     :^: NegInfinity) = IndForm
simplify (Infinity    :^: Const a)
                              | a > 0  = Infinity
                              | a < 0  = Const 0
                              | a == 0 = IndForm
simplify (NegInfinity :^: Const a)
                              | a > 0  = Undefined
                              | a < 0  = Const 0
                              | a == 0 = IndForm
simplify (Infinity    :^: a)           = Undefined
simplify (a           :^: Infinity)    = Undefined
simplify (NegInfinity :^: a)           = Undefined
simplify (a           :^: NegInfinity) = Undefined


-- 0-swallowing rules
simplify (a       :*: Const 0) = Const 0
simplify (Const 0 :*: a      ) = Const 0
simplify (a :^: Const 0)       = Const 1
simplify (Const a :/: Const 0)
    | a > 0  = Infinity
    | a < 0  = NegInfinity
    | a == 0 = IndForm
simplify (a :/: Const 0) = (simplify a) :*: Infinity
simplify (Const 0 :/: a) = Const 0 -- make this work with inf

simplify (Const 1 :^: a) = Const 1

-- add rules for rational-like patterns here:
simplify ((Const a :/: Const b) :/: Const c)
    | b /= 0 && c /= 0   = Const a :/: Const (b*c)
simplify (Const a :/: (Const b :/: Const c))
    | b /= 0 && c /= 0   = Const (a*c) :/: Const b
simplify ((Const a :/: Const b) :*: Const c)
    | b /= 0             = Const (a*c) :/: Const b
simplify ((Const a :/: Const b) :+: (Const c :/: Const d))
    | b /= 0 && d /= 0   = Const (a*d + c*b) :/: Const (b*d)
simplify ((Const a :/: Const b) :*: (Const c :/: Const d))
    | b /= 0 && d /= 0   = Const (a*c) :/: Const (b*d)
simplify ((Const a :/: Const b) :/: (Const c :/: Const d))
    | b /= 0 && d /= 0 && c /= 0 = Const (a*d) :/: Const (b*c)

-- associativity rules
--simplify (a :+: (b :+: c)) = (simplify a) :+: (simplify b) :+: (simplify c)
--simplify ((a :+: b) :+: c) = (simplify a) :+: (simplify b) :+: (simplify c)
--simplify (a :*: (b :*: c)) = (simplify a) :*: (simplify b) :*: (simplify c)
--simplify ((a :*: b) :*: c) = (simplify a) :*: (simplify b) :*: (simplify c)

-- Catchall patterns bellow
simplify (a :/: b) = (simplify a) :/: (simplify b)
simplify (a :^: b) = (simplify a) :^: (simplify b)
simplify (a :*: b) = (simplify a) :*: (simplify b)
simplify (a :+: b) = (simplify a) :+: (simplify b)
simplify (Ln a)    = Ln (simplify a)
simplify (Sin a)   = Sin (simplify a)
simplify (Cos a)   = Cos (simplify a)
simplify (Tan a)   = Tan (simplify a)
simplify (Sec a)   = Sec (simplify a)
simplify (Csc a)   = Csc (simplify a)
simplify (Cot a)   = Cot (simplify a)
simplify x         = id x


fullSimplify :: (Ord a, Num a, Eq a, Floating a) => Expr a -> Expr a
fullSimplify expr = fullSimplify' expr (Const 0)
    where fullSimplify' cur last
            | cur == last = cur
            | otherwise   = let cur' = simplify cur
                            in  fullSimplify' cur' cur
                            

