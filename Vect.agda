module AgdaUtils.Vect where

open import AgdaUtils.Basics
open import AgdaUtils.Prod
open import AgdaUtils.Nat
open import AgdaUtils.Fin

data vect (A : Set) : nat -> Set where
  [] : vect A Zero
  _::_ : {n : nat} -> A -> vect A n -> vect A (Suc n)

infixr 70 _::_

_!_ : {A : Set} {n : nat} -> vect A n -> fin n -> A
[]     ! ()
x :: v ! FZ   = x
x :: v ! FS f = v ! f

infixl 60 _!_

_++_ : {A : Set} {n m : nat} -> vect A n -> vect A m -> vect A (n + m)
[]        ++ bs = bs
(x :: as) ++ bs = x :: as ++ bs

infixr 70 _++_

insertAt : {A : Set} {n : nat} -> fin (Suc n) -> vect A n -> A -> vect A (Suc n)
insertAt FZ      vect        a = a :: vect
insertAt (FS ()) []          a
insertAt (FS f)  (b :: vect) a = b :: (insertAt f vect a)

replace : {A : Set} {n : nat} -> fin n -> vect A n -> A -> vect A n
replace FZ     (b :: as) a = a :: as
replace (FS x) (b :: as) a = b :: replace x as a

map : {A B : Set} {n : nat} -> (A -> B) -> vect A n -> vect B n
map f []        = []
map f (a :: as) = f a :: map f as

filter : {A : Set} {n : nat} {p : A -> Set} -> ((a : A) -> decide (p a)) -> vect A n -> nat * vect A
filter p []        = Zero , []
filter p (a :: as) with p a | filter p as
filter p (a :: as) | Yes _  | n , as' = Suc n , a :: as'
filter p (a :: as) | No _   | n , as' = n , as'

foldr : {A B : Set} {n : nat} -> (A -> B -> B) -> B -> vect A n -> B
foldr f b []        = b
foldr f b (a :: as) = f a (foldr f b as)

all : {A : Set} {n : nat} -> (A -> Set) -> vect A n -> Set
all P []        = Unit
all P (a :: as) = P a × all P as

-- equality 

vectEq : {A : Set} {n : nat} -> equality A -> equality (vect A n)
vectEq aeq []        []          = Yes Refl
vectEq aeq (a :: as) (b :: bs)   with aeq a b | vectEq aeq as bs
vectEq aeq (a :: as) (.a :: .as) | Yes Refl   | Yes Refl = Yes Refl
vectEq aeq (a :: as) (.a :: bs)  | Yes Refl   | No neq   = No (lemma a as bs neq)
  where 
    lemma : {A : Set} {n : nat} (a : A) (as bs : vect A n) -> not (as == bs) -> not (a :: as == a :: bs)
    lemma a as .as neq Refl = neq Refl
vectEq aeq (a :: as) (b :: bs)   | No neq     | _        = No (lemma a b as bs neq)
  where 
    lemma : {A : Set} {n : nat} (a b : A) (as bs : vect A n) -> not (a == b) -> not (a :: as == b :: bs)
    lemma a .a as .as neq Refl = neq Refl

-- Lemmas

lookupInsertAt : {A : Set} {n : nat} (vs : vect A n) (x : fin (Suc n)) (v : A) -> insertAt x vs v ! x == v
lookupInsertAt vs        FZ      v = Refl
lookupInsertAt []        (FS ()) v
lookupInsertAt (x :: vs) (FS y)  v = lookupInsertAt vs y v

insertAtFincr : {A : Set} {n : nat} (gam : vect A n) (x : fin n) (y : fin (Suc n)) (a : A) -> insertAt y gam a ! fincr y x == gam ! x
insertAtFincr (b :: gam) FZ     FZ     a = Refl
insertAtFincr (b :: gam) FZ     (FS y) a = Refl
insertAtFincr (b :: gam) (FS x) FZ     a = Refl
insertAtFincr (b :: gam) (FS x) (FS y) a = insertAtFincr gam x y a

lookupInsertAtNeq : {A : Set} {n : nat} (vs : vect A n) (x y : fin (Suc n)) (a : A) (npf : not (y == x)) -> insertAt x vs a ! y == vs ! fdecr x y npf
lookupInsertAtNeq vs        FZ      FZ      a npf with npf Refl
lookupInsertAtNeq vs        FZ      FZ      a npf | ()
lookupInsertAtNeq []        FZ      (FS ()) a npf
lookupInsertAtNeq []        (FS ()) y       a npf
lookupInsertAtNeq (v :: vs) FZ      (FS y)  a npf = Refl
lookupInsertAtNeq (v :: vs) (FS x)  FZ      a npf = Refl
lookupInsertAtNeq (v :: vs) (FS x)  (FS y)  a npf = lookupInsertAtNeq vs x y a (neqFS npf)

replaceLookup : {A : Set} {n : nat} (x : fin n) (as : vect A n) (a : A) -> replace x as a ! x == a
replaceLookup FZ     (b :: as) a = Refl
replaceLookup (FS x) (b :: as) a = replaceLookup x as a

mapLookup : {A B : Set} {n : nat} (f : A -> B) (as : vect A n) (x : fin n) -> map f as ! x == f (as ! x)
mapLookup f (a :: as) FZ     = Refl
mapLookup f (a :: as) (FS x) = mapLookup f as x

mapInsertAt : {A B : Set} {n : nat} (as : vect A n) (a : A) (f : A -> B) (x : fin (Suc n)) -> map f (insertAt x as a) == insertAt x (map f as) (f a)
mapInsertAt []        b f FZ      = Refl
mapInsertAt []        b f (FS ())
mapInsertAt (a :: as) b f FZ      = Refl
mapInsertAt (a :: as) b f (FS x)  rewrite mapInsertAt as b f x = Refl
