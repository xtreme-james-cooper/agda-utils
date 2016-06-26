module AgdaUtils.List where

data list (A : Set) : Set where
  [] : list A
  _::_ : A -> list A -> list A

infixr 50 _::_
