module AgdaUtils.Basics where

open import Agda.Primitive

data Falsity : Set where

not : {i : Level} -> Set i -> Set i
not x = x -> Falsity

data _==_ {i : Level} {A : Set i} (a : A) : A -> Set i where
  Refl : a == a

infix 40 _==_

{-# BUILTIN EQUALITY _==_ #-}
{-# BUILTIN REFL Refl #-}

sym : {A : Set} {a b : A} -> a == b -> b == a
sym Refl = Refl

cast : {i : Level} {A B : Set i} -> A -> A == B -> B
cast a eq rewrite eq = a

funEq : {i j : Level} {A : Set i} {B : Set j} {a b : A} (f : A -> B) -> a == b -> f a == f b
funEq f Refl = Refl

data decide {i : Level} (A : Set i) : Set i where
  Yes : A -> decide A
  No : not A -> decide A

decideNot : {i : Level} {A : Set i} -> decide A -> decide (not A)
decideNot (Yes a) = No (λ na -> na a)
decideNot (No na) = Yes na

equality : Set -> Set
equality A = (a b : A) -> decide (a == b)

data Unit : Set where
  TT : Unit

unitSingleton : (x : Unit) -> x == TT
unitSingleton TT = Refl

-- inspect

record Reveal_·_is_ {a b : Level} {A : Set a} {B : A -> Set b} (f : (x : A) -> B x) (x : A) (y : B x) : Set (a ⊔ b) where
  constructor [_]
  field eq : f x == y

inspect : {a b : Level} {A : Set a} {B : A -> Set b} (f : (x : A) -> B x) (x : A) -> Reveal f · x is f x
inspect f x = [ Refl ]

