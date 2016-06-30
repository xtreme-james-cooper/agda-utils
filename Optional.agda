module AgdaUtils.Optional where

data option (A : Set) : Set where
  [_] : A -> option A
  ∅ : option A  

_~>_ : (A B : Set) -> Set 
A ~> B = A -> option B

infixr 10 _~>_
