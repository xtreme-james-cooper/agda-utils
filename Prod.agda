module AgdaUtils.Prod where

data _\/_ (A B : Set) : Set where
  InL : A -> A \/ B
  InR : B -> A \/ B

infix 30 _\/_

data _*_ (A : Set) (B : A -> Set) : Set where
  _,_ : (a : A) (b : B a) -> A * B

infixr 30 _*_

fst : {A : Set} {B : A -> Set} -> A * B -> A
fst (a , b) = a

data _×_ (A B : Set) : Set where
  _,_ : A -> B -> A × B

infixr 30 _×_
infixr 20 _,_
