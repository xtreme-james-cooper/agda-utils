module AgdaUtils.List where

data list (A : Set) : Set where
  [] : list A
  _::_ : A -> list A -> list A

infixr 50 _::_

_++_ : {A : Set} -> list A -> list A -> list A
[]      ++ bs = bs
a :: as ++ bs = a :: (as ++ bs)

infixl 40 _++_
