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

~ : bool -> bool
~ True  = False
~ False = True

andTrue : {b : bool} -> (b and True) == b
andTrue {True}  = Refl
andTrue {False} = Refl

andFalse : {b : bool} -> (b and False) == False
andFalse {True}  = Refl
andFalse {False} = Refl

negNeg : {b : bool} -> ~ (~ b) == b
negNeg {True}  = Refl
negNeg {False} = Refl

negNeq : {b : bool} -> not (~ b == b)
negNeq {True}  ()
negNeq {False} ()

-- setification

truthify : bool -> Set
truthify True  = Unit
truthify False = Falsity

boolify : {P : Set} -> decide P -> bool
boolify (Yes x) = True
boolify (No x)  = False
