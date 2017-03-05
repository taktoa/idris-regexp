module Regex.Type

import Pruviloj.Core
import Pruviloj.Derive.DecEq

infixl 7 :.:
infixl 6 :|:
infixl 6 :&:

%default total

||| The type of regular expressions over a given token type.
public export
data Regex : Type where
  ||| The regular expression matching nothing
  Ø     : Regex
  ||| The regular expression matching an empty string
  Ɛ     : Regex
  ||| The regular expression matching a single token
  Tok   : Char -> Regex
  ||| Kleene star
  Star  : Regex -> Regex
  ||| Union of two regular expressions
  (:|:) : Regex -> Regex -> Regex
  ||| Complement of regular expressions
  Comp  : Regex -> Regex
  ||| Intersection of two regular expressions
  (:&:) : Regex -> Regex -> Regex
  ||| Sequence one regular expression after another
  (:.:) : Regex -> Regex -> Regex

||| Decidable equality on regular expressions
public export
regexDecEq : (r : Regex) -> (s : Regex) -> Dec (r = s)
%runElab (deriveDecEq `{regexDecEq})

implementation DecEq Regex where
  decEq a b = regexDecEq a b

-- implementation Functor Regex where
--   map f Ø         = Ø
--   map f Ɛ         = Ɛ
--   map f (Tok t)   = Tok (f t)
--   map f (Comp r)  = Comp (map f r)
--   map f (Star r)  = Star (map f r)
--   map f (r :|: s) = (map f r) :|: (map f s)
--   map f (r :&: s) = (map f r) :&: (map f s)
--   map f (r :.: s) = (map f r) :.: (map f s)
