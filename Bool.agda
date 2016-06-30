module AgdaUtils.Bool where

open import AgdaUtils.Basics

data bool : Set where
  True : bool
  False : bool

boolEq : equality bool
boolEq True  True  = Yes Refl
boolEq True  False = No (λ ())
boolEq False True  = No (λ ())
boolEq False False = Yes Refl

_and_ : bool -> bool -> bool
True  and y = y
False and y = False

infix 70 _and_

andTrue : {b : bool} -> (b and True) == b
andTrue {True}  = Refl
andTrue {False} = Refl

andFalse : {b : bool} -> (b and False) == False
andFalse {True}  = Refl
andFalse {False} = Refl


