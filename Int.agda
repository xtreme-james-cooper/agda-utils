module AgdaUtils.Int where

data int : Set where
  Zero : int
  Suc : int -> int
  Pred : int -> int
