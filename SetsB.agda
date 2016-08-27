module AgdaUtils.SetsB where

open import AgdaUtils.Basics

data set (A : Set) : Set where
  Empty : set A
  Insert : A -> set A -> set A

data _∈_ {A : Set} (a : A) : set A -> Set where
  Here : {as : set A} -> a ∈ Insert a as
  There : {b : A} {as : set A} -> a ∈ as -> a ∈ Insert b as

infix 50 _∈_

ninUp : {A : Set} {a b : A} {as : set A} -> not (b == a) -> not (a ∈ as) -> not (a ∈ Insert b as)
ninUp neq nin Here        = neq Refl
ninUp neq nin (There mem) = nin mem

contains? : {A : Set} -> equality A -> (as : set A) (a : A) -> decide (a ∈ as)
contains? aeq Empty          a = No (λ ())
contains? aeq (Insert b as)  a with aeq b a 
contains? aeq (Insert .a as) a | Yes Refl = Yes Here
contains? aeq (Insert b as)  a | No neq   with contains? aeq as a
contains? aeq (Insert b as)  a | No neq   | Yes mem = Yes (There mem)
contains? aeq (Insert b as)  a | No neq   | No nmem = No (ninUp neq nmem)

_∪_ : {A : Set} -> set A -> set A -> set A
Empty       ∪ bs = bs
Insert a as ∪ bs = Insert a (as ∪ bs)

infix 60 _∪_

nmemUnionFst : {A : Set} (a : A) (as bs : set A) -> not (a ∈ as ∪ bs) -> not (a ∈ as)
nmemUnionFst a Empty          bs nmem ()
nmemUnionFst a (Insert .a as) bs nmem Here        = nmem Here
nmemUnionFst a (Insert b as)  bs nmem (There mem) = nmemUnionFst a as bs (λ z -> nmem (There z)) mem

nmemUnionSnd : {A : Set} (a : A) (as bs : set A) -> not (a ∈ as ∪ bs) -> not (a ∈ bs)
nmemUnionSnd a Empty         bs nmem mem = nmem mem
nmemUnionSnd a (Insert b as) bs nmem mem = nmemUnionSnd a as bs (λ z -> nmem (There z)) mem
