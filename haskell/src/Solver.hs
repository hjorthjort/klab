module Solver where

import Data.Maybe (catMaybes)
import Safe       (maximumMay)

import Gas

-- percolates ITEs to the top
normaliseStep :: VariableFreeGasExpr -> VariableFreeGasExpr
normaliseStep (Nullary n) = Nullary n
normaliseStep (Unary op (ITE c e f)) =
  normaliseStep (ITE c ope opf)
  where ope = Unary op e
        opf = Unary op f
normaliseStep (Unary op e) = Unary op e'
  where e' = normaliseStep e
normaliseStep (Binary op (ITE c e f) g) =
  normaliseStep (ITE c eg fg)
  where eg = Binary op e g
        fg = Binary op f g
normaliseStep (Binary op f (ITE c e g)) =
  normaliseStep (ITE c fe fg)
  where fe = Binary op f e
        fg = Binary op f g
normaliseStep (Binary op e f) = Binary op e' f'
  where e' = normaliseStep e
        f' = normaliseStep f
normaliseStep (ITE c e f) = ITE c e' f'
  where e' = normaliseStep e
        f' = normaliseStep f

unnormaliseStep :: (Show f, Ord f) => GasExpr f -> GasExpr f
unnormaliseStep (Nullary n) = Nullary n
unnormaliseStep (Unary op e) = Unary op e'
  where e' = unnormaliseStep e
unnormaliseStep (Binary op e f) = Binary op e' f'
  where e' = unnormaliseStep e
        f' = unnormaliseStep f
unnormaliseStep (ITE c (Binary op e f) (Binary op' g h))
  | op == op' && f == h
    = Binary op (ITE c e' g') f'
  | op == op' && e == g
    = Binary op g' (ITE c f' h')
  | otherwise
    = (ITE c (Binary op e' f') (Binary op' g' h'))
  where e' = unnormaliseStep e
        f' = unnormaliseStep f
        g' = unnormaliseStep g
        h' = unnormaliseStep h
unnormaliseStep (ITE c e f) = ITE c e' f'
  where e' = unnormaliseStep e
        f' = unnormaliseStep f

cosolveStep :: ConstantGasExpr -> ConstantGasExpr
cosolveStep (Nullary n) = Nullary n
cosolveStep (Unary op e) = Unary op e'
  where e' = cosolveStep e
cosolveStep (Binary op e f) = Binary op e' f'
  where e' = cosolveStep e
        f' = cosolveStep f
cosolveStep (ITE p
             (ITE p'
              (Nullary (Value a))
              (Nullary (Value b)))
             (ITE p''
              (Nullary (Value c))
              (Nullary (Value d))))
  | p' == p'' && a - b == c - d  && a > b =
    let e = a - b in
      (Binary Add
       (ITE p'
        (Nullary $ Value e)
        (Nullary $ Value 0))
       (ITE p
        (Nullary $ Value b)
        (Nullary $ Value d)))
  | p' == p'' && b - a == d - c && a < b =
    let e = b - a in
      (Binary Add
       (ITE p'
        (Nullary $ Value 0)
        (Nullary $ Value e))
       (ITE p
        (Nullary $ Value a)
        (Nullary $ Value c)))
  | otherwise = (ITE p
                 (ITE p'
                  (Nullary (Value a))
                  (Nullary (Value b)))
                 (ITE p''
                  (Nullary (Value c))
                  (Nullary (Value d))))
cosolveStep (ITE p e f) = ITE p e' f'
  where e' = cosolveStep e
        f' = cosolveStep f

iteratedFix :: (Eq a) => (a -> a) -> a -> a
iteratedFix f x = let x' = f x in
                    if x' == x then x else iteratedFix f x'

normalise :: VariableFreeGasExpr -> VariableFreeGasExpr
normalise = iteratedFix normaliseStep

unnormalise :: VariableFreeGasExpr -> VariableFreeGasExpr
unnormalise = iteratedFix unnormaliseStep

cosolve :: ConstantGasExpr -> ConstantGasExpr
cosolve = iteratedFix (unnormaliseStep . cosolveStep)

solve :: Int -> VariableFreeGasExpr -> ConstantGasExpr
solve maxGas = (solveLeaves maxGas) . normalise

-- only works for normalised GasExpr
solveLeaves :: Int -> VariableFreeGasExpr -> ConstantGasExpr
solveLeaves maxGas (ITE c e f) = ITE c e' f'
  where e' = solveLeaves maxGas e
        f' = solveLeaves maxGas f
solveLeaves maxGas e =
  Nullary (Value maxOfMins)
  where Just maxOfMins = maximumMay $ [minG]
                         ++ (catMaybes
                         $ (minimiseG maxGas)
                              <$> (findCallSubexprs e))
        Just minG = minimiseG maxGas e

evalUnOp :: UnOp -> Int -> Int
evalUnOp SixtyFourth x = quot x 64

evalBinOp :: BinOp -> Int -> Int -> Int
evalBinOp Add x y = x + y
evalBinOp Sub x y = x - y
evalBinOp Mul x y = x * y

-- only works for unconditional GasExpr
eval :: VariableFreeGasExpr -> Int -> Int
eval (Nullary (Value StartGas)) vg = vg
eval (Nullary (Value (Literal n))) _ = n
eval (Unary op e) vg = (evalUnOp op) (eval e vg)
eval (Binary op e f) vg = (evalBinOp op) (eval e vg) (eval f vg)
eval (ITE _ _ _ ) _ = error "only works for unconditional GasExpr"

-- only works for unconditional GasExpr
minimiseG :: Int -> VariableFreeGasExpr -> Maybe Int
minimiseG maxGas e = findInput (eval e) (>=0) [1..maxGas]

findInput :: (a -> b) -> (b -> Bool) -> [a] -> Maybe a
findInput _ _ [] = Nothing
findInput f p (x:xs) = if p (f x) then Just x else findInput f p xs

-- only works for unconditional GasExpr
findCallSubexprs :: VariableFreeGasExpr -> [VariableFreeGasExpr]
findCallSubexprs (Binary Sub (Binary Sub a (Unary SixtyFourth b)) c)
  = if a == b then [Binary Sub (Binary Sub a (Unary SixtyFourth b)) c]
                   ++ findCallSubexprs a
                   ++ findCallSubexprs c
    else (findCallSubexprs a
           ++ findCallSubexprs b
           ++ findCallSubexprs c)
findCallSubexprs (Nullary _) = []
findCallSubexprs (Unary _ a) = findCallSubexprs a
findCallSubexprs (Binary _ a b) = findCallSubexprs a
                                   ++ findCallSubexprs b
findCallSubexprs (ITE _ _ _) = error "only works for unconditional GasExpr"

maxLeaf :: ConstantGasExpr -> ConstantGasExpr
maxLeaf (Nullary (Value n)) = (Nullary (Value n))
maxLeaf (ITE _ e f) = max (maxLeaf e) (maxLeaf f)
