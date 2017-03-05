module Regex.Type

import Pruviloj.Core
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
public export
regexDecEq : (tok : Type) -> (DecEq tok) => (r : Regex tok) -> (s : Regex tok) -> Dec (r = s)
%runElab (deriveDecEq `{regexDecEq})

-- regexDecEq = go
--   where
--     lemma1_alt : {x, x', y, y' : Regex tok}
--                  -> (x = x')
--                  -> Not (y = y')
--                  -> Not ((x :|: y) = (x' :|: y'))
--     lemma1_alt Refl p Refl = p Refl
--     
--     lemma2_alt : {x, x', y, y' : Regex tok}
--                  -> Not (x = x')
--                  -> (y = y')
--                  -> Not ((x :|: y) = (x' :|: y))
--     lemma2_alt p Refl Refl = p Refl
--     
--     lemma3_alt : {x, x', y, y' : Regex tok}
--                  -> Not (x = x')
--                  -> Not (y = y')
--                  -> Not ((x :|: y) = (x' :|: y'))
--     lemma3_alt p p' Refl = p Refl
--  
--     lemma1_and : {x, x', y, y' : Regex tok}
--                  -> (x = x')
--                  -> Not (y = y')
--                  -> Not ((x :&: y) = (x' :&: y'))
--     lemma1_and Refl p Refl = p Refl
--     
--     lemma2_and : {x, x', y, y' : Regex tok}
--                  -> Not (x = x')
--                  -> (y = y')
--                  -> Not ((x :&: y) = (x' :&: y))
--     lemma2_and p Refl Refl = p Refl
--     
--     lemma3_and : {x, x', y, y' : Regex tok}
--                  -> Not (x = x')
--                  -> Not (y = y')
--                  -> Not ((x :&: y) = (x' :&: y'))
--     lemma3_and p p' Refl = p Refl
--  
--     lemma1_seq : {x, x', y, y' : Regex tok}
--                  -> (x = x')
--                  -> Not (y = y')
--                  -> Not ((x :.: y) = (x' :.: y'))
--     lemma1_seq Refl p Refl = p Refl
--     
--     lemma2_seq : {x, x', y, y' : Regex tok}
--                  -> Not (x = x')
--                  -> (y = y')
--                  -> Not ((x :.: y) = (x' :.: y))
--     lemma2_seq p Refl Refl = p Refl
--     
--     lemma3_seq : {x, x', y, y' : Regex tok}
--                  -> Not (x = x')
--                  -> Not (y = y')
--                  -> Not ((x :.: y) = (x' :.: y'))
--     lemma3_seq p p' Refl = p Refl
--       
--     go : (DecEq tok) => (r : Regex tok) -> (s : Regex tok) -> Dec (r = s)
--     go Ø Ø = Yes Refl
--     go Ɛ Ɛ = Yes Refl
--     go (Tok t1) (Tok t2) with (decEq t1 t2)
--       | Yes p = Yes (cong p)
--       | No  c = No (\Refl => c Refl)
--     go (Comp r1) (Comp r2) with (go r1 r2)
--       | Yes p = Yes (cong p)
--       | No  c = No (\Refl => c Refl)
--     go (Star r1) (Star r2) with (go r1 r2)
--       | Yes p = Yes (cong p)
--       | No  c = No (\Refl => c Refl)
--     go (r1 :|: s1) (r2 :|: s2) with (go r1 r2)
--       go (r :|: s1) (r :|: s2) | (Yes Refl) with (go s1 s2)
--         go (r :|: s ) (r :|: s ) | (Yes Refl) | (Yes Refl) = Yes Refl
--         go (r :|: s1) (r :|: s2) | (Yes Refl) | (No p)     = No (\eq => lemma1_alt Refl p eq)
--       go (r1 :|: s1) (r2 :|: s2) | (No p) with (go s1 s2)
--         go (r1 :|: s ) (r2 :|: s ) | (No p) | (Yes Refl) = No (\eq => lemma2_alt p Refl eq)
--         go (r1 :|: s1) (r2 :|: s2) | (No p) | (No p')    = No (\eq => lemma3_alt p p' eq)
--     go (r1 :&: s1) (r2 :&: s2) with (go r1 r2)
--       go (r :&: s1) (r :&: s2) | (Yes Refl) with (go s1 s2)
--         go (r :&: s ) (r :&: s ) | (Yes Refl) | (Yes Refl) = Yes Refl
--         go (r :&: s1) (r :&: s2) | (Yes Refl) | (No p)     = No (\eq => lemma1_and Refl p eq)
--       go (r1 :&: s1) (r2 :&: s2) | (No p) with (go s1 s2)
--         go (r1 :&: s ) (r2 :&: s ) | (No p) | (Yes Refl) = No (\eq => lemma2_and p Refl eq)
--         go (r1 :&: s1) (r2 :&: s2) | (No p) | (No p')    = No (\eq => lemma3_and p p' eq)
--     go (r1 :.: s1) (r2 :.: s2) with (go r1 r2)
--       go (r :.: s1) (r :.: s2) | (Yes Refl) with (go s1 s2)
--         go (r :.: s ) (r :.: s ) | (Yes Refl) | (Yes Refl) = Yes Refl
--         go (r :.: s1) (r :.: s2) | (Yes Refl) | (No p)     = No (\eq => lemma1_seq Refl p eq)
--       go (r1 :.: s1) (r2 :.: s2) | (No p) with (go s1 s2)
--         go (r1 :.: s ) (r2 :.: s ) | (No p) | (Yes Refl) = No (\eq => lemma2_seq p Refl eq)
--         go (r1 :.: s1) (r2 :.: s2) | (No p) | (No p')    = No (\eq => lemma3_seq p p' eq)
--     go owise1 owise2 = No ?fixme_go

--   | Yes p = regexDecEq s1 s2
--   | No  c = No (\Refl => c Refl)

-- implementation (DecEq tok) => DecEq (Regex tok) where
--   decEq {tok} a b = regexDecEq tok a b

implementation Functor Regex where
  map f Ø         = Ø
  map f Ɛ         = Ɛ
  map f (Tok t)   = Tok (f t)
  map f (Comp r)  = Comp (map f r)
  map f (Star r)  = Star (map f r)
  map f (r :|: s) = (map f r) :|: (map f s)
  map f (r :&: s) = (map f r) :&: (map f s)
  map f (r :.: s) = (map f r) :.: (map f s)
