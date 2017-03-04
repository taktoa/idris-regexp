module Regex.Type

import Pruviloj.Derive.DecEq

infixl 7 :.:
infixl 6 :|:
infixl 6 :&:

%default total

||| The type of regular expressions over a given token type.
public export data Regex : Type -> Type where
  ||| The regular expression matching nothing
  Ø     : Regex tok
  ||| The regular expression matching an empty string
  Ɛ     : Regex tok
  ||| The regular expression matching a single token
  Tok   : tok -> Regex tok
  ||| Complement of regular expressions
  Comp  : Regex tok -> Regex tok
  ||| Kleene star
  Star  : Regex tok -> Regex tok
  ||| Union of two regular expressions
  (:|:) : Regex tok -> Regex tok -> Regex tok
  ||| Intersection of two regular expressions
  (:&:) : Regex tok -> Regex tok -> Regex tok
  ||| Sequence one regular expression after another
  (:.:) : Regex tok -> Regex tok -> Regex tok

||| Decidable equality on regular expressions
private
regexDecEq : {tok : Type} -> (DecEq tok)
             => (r : Regex tok) -> (s : Regex tok) -> Dec (r = s)
%runElab (deriveDecEq `{regexDecEq})

implementation (DecEq tok) => DecEq (Regex tok) where
  decEq = regexDecEq

implementation Functor Regex where
  map f Ø         = Ø
  map f Ɛ         = Ɛ
  map f (Tok t)   = Tok (f t)
  map f (Comp r)  = Comp (map f r)
  map f (Star r)  = Star (map f r)
  map f (r :|: s) = (map f r) :|: (map f s)
  map f (r :&: s) = (map f r) :&: (map f s)
  map f (r :.: s) = (map f r) :.: (map f s)
