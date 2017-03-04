module Main

import Control.Isomorphism
import Pruviloj.Derive.DecEq

infixl 7 :.:
infixl 6 :|:
infixl 6 :&:

%default total

||| The type of regular expressions over a given token type.
data Regex : Type -> Type where
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

-- %runElab (deriveDecEq `{{Regex}})

implementation Functor Regex where
  map f Ø         = Ø
  map f Ɛ         = Ɛ
  map f (Tok t)   = Tok (f t)
  map f (Comp r)  = Comp (map f r)
  map f (Star r)  = Star (map f r)
  map f (r :|: s) = (map f r) :|: (map f s)
  map f (r :&: s) = (map f r) :&: (map f s)
  map f (r :.: s) = (map f r) :.: (map f s)

mutual
  ||| FIXME: doc
  data LPlus : List tok -> Regex tok -> Type where
    SP : (DecEq tok)
         => Matches {tok} s r
         -> LPlus {tok} s r
    CP : (DecEq tok)
         => (s1 ++ s2 = s)
         -> Matches {tok} s1 r
         -> LPlus {tok} s2 r
         -> LPlus {tok} s r

  ||| The language for a given generalized regular expression.
  Matches : (DecEq tok) => List tok -> Regex tok -> Type
  Matches {tok} = Lang
    where
      Lang : List tok -> Regex tok -> Type
      Lang x Ø         = Void
      Lang x Ɛ         = ()
      Lang x (Tok t)   = (x = [t])
      Lang x (Comp r)  = Lang x r -> Void
      Lang x (Star r)  = Either () (LPlus x r)
      Lang x (r :|: s) = Either (Lang x r) (Lang x s)
      Lang x (r :&: s) = (Lang x r, Lang x s)
      Lang x (r :.: s) = (p, q : List tok) -> (p ++ q = x, Lang p r, Lang q s)

||| A proof that the given regular expressions are equivalent.
Equiv : (DecEq tok) => Regex tok -> Regex tok -> Type
Equiv {tok} r s = (str : List tok) -> (Matches str r, Matches str s)

||| If the given regular expression contains the empty string, the result is Ɛ.
||| Otherwise, the result is Ø.
nullable : Regex tok -> Regex tok
nullable = \x => if go x then Ɛ else Ø
  where
    go : Regex t -> Bool
    go Ø         = False
    go Ɛ         = True
    go (Tok t)   = False
    go (Comp r)  = not (go r)
    go (Star r)  = True
    go (r :|: s) = go r || go s
    go (r :&: s) = go r && go s
    go (r :.: s) = go r && go s

||| A type-level witness to the claim that a given regular expression
||| is nullable
Nullable : (DecEq tok) => Regex tok -> Type
Nullable r = Matches [] r

||| FIXME: doc
absurdIso : (Uninhabited t) => Iso Void t
absurdIso = ?fixme_absurdIso

||| FIXME: doc
nullableWorks : (DecEq tok) => (r : Regex tok)
                -> Iso (Nullable r) (nullable r = Ɛ)
nullableWorks Ø         = ?fixme71_1
nullableWorks Ɛ         = ?fixme71_2
nullableWorks (Tok x)   = ?fixme71_3
nullableWorks (Comp x)  = ?fixme71_4
nullableWorks (Star x)  = ?fixme71_5
nullableWorks (x :|: y) = ?fixme71_6
nullableWorks (x :&: y) = ?fixme71_7
nullableWorks (x :.: y) = ?fixme71_8

||| The Brzozowski derivative of a regular expression
deriv : (Eq tok) => tok -> Regex tok -> Regex tok
deriv a Ø         = Ø
deriv a Ɛ         = Ø
deriv a (Tok t)   = if t == a then Ɛ else Ø
deriv a (Comp r)  = Comp (deriv a r)
deriv a (Star r)  = deriv a r :.: Star r
deriv a (r :|: s) = deriv a r :|: deriv a s
deriv a (r :&: s) = deriv a r :&: deriv a s
deriv a (r :.: s) = let r' = deriv a r
                        s' = deriv a s
                    in (r' :.: s) :|: (nullable r :.: s')

||| The Brzozowski derivative with respect to strings
derivative : (Eq tok) => List tok -> Regex tok -> Regex tok
derivative []        r = r
derivative (a :: as) r = deriv a (derivative as r)

||| FIXME: doc
derivativeWorks : (DecEq tok, Eq tok)
                  => (str : List tok) -> (r : Regex tok)
                  -> Iso (Matches str r) (Matches [] (derivative str r))
derivativeWorks str Ø         = ?fixme72_1
derivativeWorks str Ɛ         = ?fixme72_2
derivativeWorks str (Tok x)   = ?fixme72_3
derivativeWorks str (Comp x)  = ?fixme72_4
derivativeWorks str (Star x)  = ?fixme72_5
derivativeWorks str (x :|: y) = ?fixme72_6
derivativeWorks str (x :&: y) = ?fixme72_7
derivativeWorks str (x :.: y) = ?fixme72_8

main : IO ()
main = pure ()
