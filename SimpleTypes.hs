module Types where

data SrcPos = SrcPos
  deriving (Eq, Ord, Read, Show)

-- starting with stlc
data SimpleType
  = STFunction SrcPos SimpleType SimpleType
  | STNamed SrcPos String
  deriving (Eq, Ord, Read, Show)

unifySimple :: (STUnify m) => SimpleType -> SimpleType -> m ()
unifySimple expected@(STNamed _ s) actual@(STNamed _ t) = do
  case s == t of
    True -> return ()
    False -> throwSimpleError $ Unequal expected actual
unifySimple (STFunction _ si so) (STFunction _ ti to) = do
  unifySimple si ti
  unifySimple so to
unifySimple expected actual = throwSimpleError (Unequal expected actual)

applySimple :: (STUnify m) => SimpleType -> SimpleType -> m SimpleType
applySimple (STFunction _ expectedInput output) actualInput = do
  unifySimple expectedInput actualInput
  return output
applySimple applier@(STNamed _ _) _ = throwSimpleError (NotAFunction applier)

data SimpleTypeError
  = Unequal SimpleType SimpleType
  | NotAFunction SimpleType
  deriving (Eq, Ord, Read, Show)

class Monad m => STUnify m where
  throwSimpleError :: SimpleTypeError -> m a
