||| A port of Edward Kmett's `machines` library to Idris.
module Machines


data Mealy : Type -> Type -> Type where
  MkMealy : (a -> (b, Mealy a b)) -> Mealy a b
