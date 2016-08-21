module AgdaUtils.Order where

open import AgdaUtils.Basics
open import AgdaUtils.Prod

data order : Set where
  LT : order
  EQ : order
  GT : order

orderEq : equality order
orderEq LT LT = Yes Refl
orderEq LT EQ = No (λ ())
orderEq LT GT = No (λ ())
orderEq EQ LT = No (λ ())
orderEq EQ EQ = Yes Refl
orderEq EQ GT = No (λ ())
orderEq GT LT = No (λ ())
orderEq GT EQ = No (λ ())
orderEq GT GT = Yes Refl

antisymmetric : {A : Set} -> (A -> A -> order) -> Set
antisymmetric {A} comp = (a b : A) -> (comp a b == EQ -> a == b) × (not (comp a b == EQ) -> not (a == b)) × (comp a b == LT -> comp b a == GT)

transitive : {A : Set} -> (A -> A -> order) -> Set
transitive {A} comp = (a b c : A) -> comp a b == LT -> comp b c == LT -> comp a c == LT

data ordering (A : Set) : Set where
  Ordering : (comp : A -> A -> order) -> antisymmetric comp -> transitive comp -> ordering A
