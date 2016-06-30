module AgdaUtils.Optional where

data option (A : Set) : Set where
  [_] : A -> option A
  ∅ : option A  
