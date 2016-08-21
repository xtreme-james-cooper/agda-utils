module AgdaUtils.List where

open import AgdaUtils.Basics
open import AgdaUtils.Prod

data list (A : Set) : Set where
  [] : list A
  _::_ : A -> list A -> list A

infixr 50 _::_

_++_ : {A : Set} -> list A -> list A -> list A
[]      ++ bs = bs
a :: as ++ bs = a :: (as ++ bs)

infixr 40 _++_

appendNil : {A : Set} (as : list A) -> as ++ [] == as
appendNil []        = Refl
appendNil (a :: as) rewrite appendNil as = Refl

appendAssoc : {A : Set} (as bs cs : list A) -> (as ++ bs) ++ cs == as ++ bs ++ cs
appendAssoc []        bs cs = Refl
appendAssoc (a :: as) bs cs rewrite appendAssoc as bs cs = Refl

all : {A : Set} -> (A -> Set) -> list A -> Set
all P []        = Unit
all P (a :: as) = P a × all P as
