{-# Language TemplateHaskell #-}
{-# Language ViewPatterns #-}

module Gas where

import Control.Lens hiding (op)
import Control.Monad.State.Strict
import Data.List (intercalate)
import Data.Map.Strict as Map

data (Ord f) => NullOp f = Value f
  deriving (Eq, Ord, Show)
data UnOp = SixtyFourth
  deriving (Eq, Ord, Show)
data BinOp = Add | Sub | Mul
  deriving (Eq, Ord, Show)
data Cond = Cond FormulaicString
  deriving (Eq, Ord, Show)

-- grammar for K gas expressions
-- a is the "base field"
data (Show f, Ord f) => GasExpr f =
  Nullary (NullOp f)
  | Unary UnOp (GasExpr f)
  | Binary BinOp (GasExpr f) (GasExpr f)
  | ITE Cond (GasExpr f) (GasExpr f)
  deriving (Eq, Ord, Show)

data IntOrStartGas = Literal Int | StartGas
  deriving (Eq)

instance Show IntOrStartGas where
  show StartGas = "VGas"
  show n = show n

type ConstantGasExpr = GasExpr Int
type VariableFreeGasExpr = GasExpr IntOrStartGas

-- coerceToConstant :: VariableFreeGasExpr -> ConstantGasExpr
-- coerceToConstant (Nullary (Value (Literal n))) = Nullary (Value n)
-- coerceToConstant (Unary op e) = Unary op (coerceToConstant e)
-- coerceToConstant (Binary op e e') = Binary op (coerceToConstant e) (coerceToConstant e')
-- coerceToConstant (ITE c e e') = ITE c (coerceToConstant e) (coerceToConstant e')

promoteFromConstant :: ConstantGasExpr -> VariableFreeGasExpr
promoteFromConstant (Nullary (Value (Literal n))) = Nullary (Value n)
promoteFromConstant
coerceToConstant (Unary op e) = Unary op (coerceToConstant e)
coerceToConstant (Binary op e e') = Binary op (coerceToConstant e) (coerceToConstant e')
coerceToConstant (ITE c e e') = ITE c (coerceToConstant e) (coerceToConstant e')
-- a formatted K formula with typed variables
data FormulaicString = FormulaicString
  { _formula :: String,
    _types   :: Map String String
  }
  deriving (Eq, Ord, Show)

instance Ord IntOrStartGas where
  StartGas <= _ = True
  m <= n        = m <= n

data StratificationMap f = StratificationMap
 { _stratMap   :: Map (GasExpr f) Int,
   _nextIndex  :: Int,
   _stratLabel :: String,
   _stratTypes :: Map String String
 }

makeLenses ''StratificationMap
makeLenses ''FormulaicString

type Stratification f a = State (StratificationMap f) a

bracket :: String -> String
bracket s = "( " ++ s ++ " )"

unparse :: (Show f, Ord f) => (Maybe (StratificationMap f)) -> (GasExpr f) -> String
unparse msm expr =
  let (sm, tag, ts) = case msm of
        Just x  -> (x ^. stratMap,
                    x ^. stratLabel,
                    x ^. stratTypes)
        Nothing -> (mempty, "", mempty)
  in case Map.lookup expr sm of
    Just i -> tag ++ show i ++ formatKArgs (Map.toList ts)
    Nothing -> case expr of
      -- (Nullary (Value StartGas)) -> "VGas"
      (Nullary (Value x)) -> show x
      (Unary SixtyFourth e) -> (bracket $ unparse msm e) ++ " /Int 64"
      (Binary op e f) -> bracket (s ++ opstr ++ t)
        where s = unparse msm e
              t = unparse msm f
              opstr = case op of
                        Add -> " +Int "
                        Sub -> " -Int "
                        Mul -> " *Int "
      (ITE (Cond c) e f) ->
        "(" ++ "#if " ++ (c ^. formula) ++
               " #then " ++ s ++
               " #else " ++ t ++
               " #fi" ++ ")"
        where s = unparse msm e
              t = unparse msm f

stratifier :: (Show f, Ord f) => (GasExpr f) -> Stratification f ()
stratifier expr = do
  smap <- get
  -- insertSoft means we deduplicate the labels
  let insertSoft = Map.insertWith (flip const)
      i = smap ^. nextIndex
      smap' = stratMap %~ (insertSoft expr i)
              $ nextIndex %~ (+1)
              $ smap
  put smap'
  case expr of
    -- should only stratify unconditional exprs
    (Unary _ e) -> do
      stratifier e
      return ()
    (Binary _ e f) -> do
      stratifier e
      stratifier f
      return ()
    (ITE (Cond c) e f) -> do
      put $
        stratTypes %~ (Map.union (c ^. types)) $
        smap'
      stratifier e
      stratifier f
      return ()
    (Nullary _) ->
      return ()

stratify :: (Show f, Ord f) => String -> (GasExpr f) -> (StratificationMap f)
stratify s e = execState (stratifier e)
  (StratificationMap
    { _stratMap   = mempty,
      _nextIndex  = 0,
      _stratLabel = s,
      _stratTypes = mempty
    })

formatStratifiedSyntax :: (Show f, Ord f) => (StratificationMap f) -> String
formatStratifiedSyntax sm =
  Map.foldlWithKey (formatStratifiedLeaf sm) "" (view stratMap sm)

formatStratifiedLeaf :: (Show f, Ord f) => (StratificationMap f) -> String -> (GasExpr f) -> Int -> String
formatStratifiedLeaf sm acc expr i =
  let args = Map.toList $ sm ^. stratTypes in acc
  ++ "syntax Int ::= \"" ++ tag ++ show i
  ++ "\" " ++ (formatAbstractKArgs args) ++ "\n"
  ++ "rule " ++ tag ++ show i ++ (formatKArgs args)
  ++ " => "
  ++ (unparse (Just sm') expr) ++ " [macro]"
  ++ "\n" ++ "\n"
  where tag = sm ^. stratLabel
        sm' = stratMap %~ (Map.delete expr) $ sm

formatAbstractKArgs :: [(String, String)] -> String
formatAbstractKArgs [] = ""
formatAbstractKArgs ts =
  "\"(\" "
  ++ (intercalate " \",\" " (snd <$> ts))
  ++ " \")\""

formatKArgs :: [(String, String)] -> String
formatKArgs [] = ""
formatKArgs ts =
  "("
  ++ (intercalate ", " (fst <$> ts))
  ++ ")"
