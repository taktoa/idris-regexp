module Main

infixl 7 :.:
infixl 6 :|:
infixl 6 :&:

%default total

||| The initial algebra in the category of generalized regular expressions.
data Regex : Type -> Type where
  ||| The regular expression matching nothing
  Ø     : Regex t
  ||| The regular expression matching an empty string
  Ɛ     : Regex t
  ||| The regular expression matching a single token
  Tok   : t -> Regex t
  ||| Complement of regular expressions
  Comp  : Regex t -> Regex t
  ||| Kleene star
  Star  : Regex t -> Regex t
  ||| Sequence one regular expression after another
  (:.:) : Regex t -> Regex t -> Regex t
  ||| Union of two regular expressions
  (:|:) : Regex t -> Regex t -> Regex t
  ||| Intersection of two regular expressions
  (:&:) : Regex t -> Regex t -> Regex t

||| If the given regular expression contains the empty string, the result is Ɛ.
||| Otherwise, the result is Ø.
nullable : Regex t -> Regex t
nullable = \x => if go x then Ɛ else Ø
  where
    go : Regex t -> Bool
    go Ø         = False
    go Ɛ         = True
    go (Tok t)   = False
    go (Comp r)  = not (go r)
    go (Star r)  = True
    go (r :.: s) = go r && go s
    go (r :|: s) = go r || go s
    go (r :&: s) = go r && go s

||| The Brzozowski derivative of a regular expression
deriv : (Eq t) => t -> Regex t -> Regex t
deriv a Ø         = Ø
deriv a Ɛ         = Ø
deriv a (Tok t)   = if t == a then Ɛ else Ø
deriv a (Comp r)  = Comp (deriv a r)
deriv a (Star r)  = deriv a r :.: Star r
deriv a (r :.: s) = let r' = deriv a r
                        s' = deriv a s
                    in (r' :.: s) :|: (nullable r :.: s')
deriv a (r :|: s) = deriv a r :|: deriv a s
deriv a (r :&: s) = deriv a r :&: deriv a s

||| The Brzozowski derivative with respect to strings
derivative : (Eq t) => List t -> Regex t -> Regex t
derivative []        r = r
derivative (a :: as) r = deriv a (derivative as r)

main : IO ()
main = pure ()
