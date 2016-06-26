module AgdaUtils.Int where

data int : Set where
  Zero : int
  Suc : int -> int
  Pred : int -> int

_plus_ : int -> int -> int
Zero plus b   = b
Suc a plus b  = Suc (a plus b)
Pred a plus b = Pred (a plus b)

_minus_ : int -> int -> int
a minus Zero   = a
a minus Suc b  = Pred (a minus b)
a minus Pred b = Suc (a minus b)

_times_ : int -> int -> int
Zero   times b = Zero
Suc a  times b = (a times b) plus b
Pred a times b = (a times b) minus b

_div_ : int -> int -> int
a div b = Zero
