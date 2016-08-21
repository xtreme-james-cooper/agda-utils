module AgdaUtils.Int where

open import AgdaUtils.Basics
open import AgdaUtils.Prod
open import AgdaUtils.Order

data intType : Set where
  Pos : intType
  Neg : intType
  Zero : intType

data normalInt : intType -> Set where
  Zero : normalInt Zero
  One : normalInt Pos
  Suc : normalInt Pos -> normalInt Pos
  NegOne : normalInt Neg
  Pred : normalInt Neg -> normalInt Neg

data int : Set where
  Int : {t : intType} -> normalInt t -> int

intEq : equality int
intEq (Int {t1} a) (Int {t2} b) with intTypeEq t1 t2
  where
    intTypeEq : equality intType
    intTypeEq Pos  Pos  = Yes Refl
    intTypeEq Pos  Neg  = No (λ ())
    intTypeEq Pos  Zero = No (λ ())
    intTypeEq Neg  Pos  = No (λ ())
    intTypeEq Neg  Neg  = Yes Refl
    intTypeEq Neg  Zero = No (λ ())
    intTypeEq Zero Pos  = No (λ ())
    intTypeEq Zero Neg  = No (λ ())
    intTypeEq Zero Zero = Yes Refl
intEq (Int {t1} a) (Int {.t1} b) | Yes Refl with normalIntEq a b
  where
    sucEqDown : {a b : normalInt Pos} -> Suc a == Suc b -> a == b
    sucEqDown Refl = Refl

    predEqDown : {a b : normalInt Neg} -> Pred a == Pred b -> a == b
    predEqDown Refl = Refl

    normalIntEq : {t : intType} -> equality (normalInt t)
    normalIntEq Zero     Zero      = Yes Refl
    normalIntEq One      One       = Yes Refl
    normalIntEq One      (Suc b)   = No (λ ())
    normalIntEq (Suc a)  One       = No (λ ())
    normalIntEq (Suc a)  (Suc b)   with normalIntEq a b
    normalIntEq (Suc a)  (Suc .a)  | Yes Refl = Yes Refl
    normalIntEq (Suc a)  (Suc b)   | No neq   = No (λ eq -> neq (sucEqDown eq))
    normalIntEq NegOne   NegOne    = Yes Refl
    normalIntEq NegOne   (Pred b)  = No (λ ())
    normalIntEq (Pred a) NegOne    = No (λ ())
    normalIntEq (Pred a) (Pred b)  with normalIntEq a b
    normalIntEq (Pred a) (Pred .a) | Yes Refl = Yes Refl
    normalIntEq (Pred a) (Pred b)  | No neq   = No (λ eq -> neq (predEqDown eq))
intEq (Int {t1} a) (Int {.t1} .a) | Yes Refl | Yes Refl = Yes Refl
intEq (Int {t1} a) (Int {.t1} b)  | Yes Refl | No neq   = No (λ eq -> neq (normEqDown eq))
  where
    normEqDown : {t : intType} {a b : normalInt t} -> Int a == Int b -> a == b
    normEqDown Refl = Refl
intEq (Int {t1} a) (Int {t2} b)   | No neq   = No (λ eq -> neq (typeEqDown eq))
  where
    typeEqDown : {t1 t2 : intType} {a : normalInt t1} {b : normalInt t2} -> Int a == Int b -> t1 == t2
    typeEqDown Refl = Refl

intComp : int -> int -> order
intComp (Int Zero)     (Int Zero)     = EQ
intComp (Int Zero)     (Int One)      = LT
intComp (Int Zero)     (Int (Suc b))  = LT
intComp (Int Zero)     (Int NegOne)   = GT
intComp (Int Zero)     (Int (Pred b)) = GT
intComp (Int One)      (Int One)      = EQ
intComp (Int One)      (Int (Suc b))  = LT
intComp (Int One)      (Int _)        = GT
intComp (Int (Suc a))  (Int (Suc b))  = intComp (Int a) (Int b)
intComp (Int (Suc a))  (Int _)        = GT
intComp (Int NegOne)   (Int NegOne)   = EQ
intComp (Int NegOne)   (Int (Pred b)) = GT
intComp (Int NegOne)   (Int _)        = LT
intComp (Int (Pred a)) (Int (Pred b)) = intComp (Int a) (Int b)
intComp (Int (Pred a)) (Int _)        = LT

intOrder : ordering int
intOrder = Ordering intComp antisym trans
  where
    antisym : antisymmetric intComp
    antisym (Int Zero)     (Int Zero)     = (λ _ -> Refl) , (λ z _ -> z Refl) , (λ ())
    antisym (Int Zero)     (Int One)      = (λ ())        , (λ _ ())          , (λ _ -> Refl)
    antisym (Int Zero)     (Int (Suc b))  = (λ ())        , (λ _ ())          , (λ _ -> Refl)
    antisym (Int Zero)     (Int NegOne)   = (λ ())        , (λ _ ())          , (λ ())
    antisym (Int Zero)     (Int (Pred b)) = (λ ())        , (λ _ ())          , (λ ())
    antisym (Int One)      (Int Zero)     = (λ ())        , (λ _ ())          , (λ ())
    antisym (Int One)      (Int One)      = (λ _ -> Refl) , (λ z _ -> z Refl) , (λ ())
    antisym (Int One)      (Int (Suc b))  = (λ ())        , (λ _ ())          , (λ _ -> Refl)
    antisym (Int One)      (Int NegOne)   = (λ ())        , (λ _ ())          , (λ ())
    antisym (Int One)      (Int (Pred b)) = (λ ())        , (λ _ ())          , (λ ())
    antisym (Int (Suc a))  (Int Zero)     = (λ ())        , (λ _ ())          , (λ ())
    antisym (Int (Suc a))  (Int One)      = (λ ())        , (λ _ ())          , (λ ())
    antisym (Int (Suc a))  (Int (Suc b))  with antisym (Int a) (Int b)
    antisym (Int (Suc a))  (Int (Suc b))  | eq , neq , rev = (λ x -> lemma a b (eq x)) , (λ z y -> neq z (lemma' a b y)) , rev
      where
        lemma : (a b : normalInt Pos) -> Int a == Int b -> Int (Suc a) == Int (Suc b)
        lemma a .a Refl = Refl
        lemma' : (a b : normalInt Pos) -> Int (Suc a) == Int (Suc b) -> Int a == Int b
        lemma' a .a Refl = Refl
    antisym (Int (Suc a))  (Int NegOne)   = (λ ())        , (λ _ ())          , (λ ())
    antisym (Int (Suc a))  (Int (Pred b)) = (λ ())        , (λ _ ())          , (λ ())
    antisym (Int NegOne)   (Int Zero)     = (λ ())        , (λ _ ())          , (λ _ -> Refl)
    antisym (Int NegOne)   (Int One)      = (λ ())        , (λ _ ())          , (λ _ -> Refl)
    antisym (Int NegOne)   (Int (Suc b))  = (λ ())        , (λ _ ())          , (λ _ -> Refl)
    antisym (Int NegOne)   (Int NegOne)   = (λ _ -> Refl) , (λ z _ -> z Refl) , (λ ())
    antisym (Int NegOne)   (Int (Pred b)) = (λ ())        , (λ _ ())          , (λ ())
    antisym (Int (Pred a)) (Int Zero)     = (λ ())        , (λ _ ())          , (λ _ -> Refl)
    antisym (Int (Pred a)) (Int One)      = (λ ())        , (λ _ ())          , (λ _ -> Refl)
    antisym (Int (Pred a)) (Int (Suc b))  = (λ ())        , (λ _ ())          , (λ _ -> Refl)
    antisym (Int (Pred a)) (Int NegOne)   = (λ ())        , (λ _ ())          , (λ _ -> Refl)
    antisym (Int (Pred a)) (Int (Pred b)) with antisym (Int a) (Int b)
    antisym (Int (Pred a)) (Int (Pred b)) | eq , neq , rev = (λ x -> lemma a b (eq x)) , (λ z y -> neq z (lemma' a b y)) , rev
      where
        lemma : (a b : normalInt Neg) -> Int a == Int b -> Int (Pred a) == Int (Pred b)
        lemma a .a Refl = Refl
        lemma' : (a b : normalInt Neg) -> Int (Pred a) == Int (Pred b) -> Int a == Int b
        lemma' a .a Refl = Refl

    trans : transitive intComp
    trans (Int Zero)     (Int Zero)     _              () _
    trans (Int Zero)     (Int One)      (Int Zero)     _ ()
    trans (Int Zero)     (Int One)      (Int One)      _ ()
    trans (Int Zero)     (Int One)      (Int (Suc c))  _  _ = Refl
    trans (Int Zero)     (Int One)      (Int NegOne)   _ ()
    trans (Int Zero)     (Int One)      (Int (Pred c)) _ ()
    trans (Int Zero)     (Int (Suc b))  (Int Zero)     _ ()
    trans (Int Zero)     (Int (Suc b))  (Int One)      _ ()
    trans (Int Zero)     (Int (Suc b))  (Int (Suc c))  _  _ = Refl
    trans (Int Zero)     (Int (Suc b))  (Int NegOne)   _ ()
    trans (Int Zero)     (Int (Suc b))  (Int (Pred c)) _ ()
    trans (Int Zero)     (Int NegOne)   _              () _
    trans (Int Zero)     (Int (Pred b)) _              () _
    trans (Int One)      (Int Zero)     _              () _
    trans (Int One)      (Int One)      _              () _
    trans (Int One)      (Int (Suc b))  (Int Zero)     _ ()
    trans (Int One)      (Int (Suc b))  (Int One)      _ ()
    trans (Int One)      (Int (Suc b))  (Int (Suc c))  _  _ = Refl
    trans (Int One)      (Int (Suc b))  (Int NegOne)   _ ()
    trans (Int One)      (Int (Suc b))  (Int (Pred c)) _ ()
    trans (Int One)      (Int NegOne)   _              () _
    trans (Int One)      (Int (Pred b)) _              () _
    trans (Int (Suc a))  (Int Zero)     _              () _
    trans (Int (Suc a))  (Int One)      _              () _
    trans (Int (Suc a))  (Int (Suc b))  (Int Zero)     _ ()
    trans (Int (Suc a))  (Int (Suc b))  (Int One)      _ ()
    trans (Int (Suc a))  (Int (Suc b))  (Int (Suc c))  lt1 lt2 = trans (Int a) (Int b) (Int c) lt1 lt2
    trans (Int (Suc a))  (Int (Suc b))  (Int NegOne)   _ ()
    trans (Int (Suc a))  (Int (Suc b))  (Int (Pred c)) _ ()
    trans (Int (Suc a))  (Int NegOne)   _              () _
    trans (Int (Suc a))  (Int (Pred b)) _              () _
    trans (Int NegOne)   (Int Zero)     (Int Zero)     _ ()
    trans (Int NegOne)   (Int Zero)     (Int One)      _  _ = Refl
    trans (Int NegOne)   (Int Zero)     (Int (Suc c))  _  _ = Refl
    trans (Int NegOne)   (Int Zero)     (Int NegOne)   _ ()
    trans (Int NegOne)   (Int Zero)     (Int (Pred c)) _ ()
    trans (Int NegOne)   (Int One)      (Int Zero)     _ ()
    trans (Int NegOne)   (Int One)      (Int One)      _ ()
    trans (Int NegOne)   (Int One)      (Int (Suc c))  _  _ = Refl
    trans (Int NegOne)   (Int One)      (Int NegOne)   _ ()
    trans (Int NegOne)   (Int One)      (Int (Pred c)) _ ()
    trans (Int NegOne)   (Int (Suc b))  (Int Zero)     _ ()
    trans (Int NegOne)   (Int (Suc b))  (Int One)      _ ()
    trans (Int NegOne)   (Int (Suc b))  (Int (Suc c))  _ _ = Refl
    trans (Int NegOne)   (Int (Suc b))  (Int NegOne)   _ ()
    trans (Int NegOne)   (Int (Suc b))  (Int (Pred c)) _ ()
    trans (Int NegOne)   (Int NegOne)   _              () _
    trans (Int NegOne)   (Int (Pred b)) _              () _
    trans (Int (Pred a)) (Int Zero)     (Int Zero)     _ ()
    trans (Int (Pred a)) (Int Zero)     (Int One)      _  _ = Refl
    trans (Int (Pred a)) (Int Zero)     (Int (Suc c))  _  _ = Refl
    trans (Int (Pred a)) (Int Zero)     (Int NegOne)   _ ()
    trans (Int (Pred a)) (Int Zero)     (Int (Pred c)) _ ()
    trans (Int (Pred a)) (Int One)      (Int Zero)     _  _ = Refl
    trans (Int (Pred a)) (Int One)      (Int One)      _ ()
    trans (Int (Pred a)) (Int One)      (Int (Suc c))  _  _ = Refl
    trans (Int (Pred a)) (Int One)      (Int NegOne)   _ ()
    trans (Int (Pred a)) (Int One)      (Int (Pred c)) _ ()
    trans (Int (Pred a)) (Int (Suc b))  (Int Zero)     _ ()
    trans (Int (Pred a)) (Int (Suc b))  (Int One)      _ ()
    trans (Int (Pred a)) (Int (Suc b))  (Int (Suc c))  _  _ = Refl
    trans (Int (Pred a)) (Int (Suc b))  (Int NegOne)   _ ()
    trans (Int (Pred a)) (Int (Suc b))  (Int (Pred c)) _ ()
    trans (Int (Pred a)) (Int NegOne)   (Int Zero)     _  _ = Refl
    trans (Int (Pred a)) (Int NegOne)   (Int One)      _  _ = Refl
    trans (Int (Pred a)) (Int NegOne)   (Int (Suc c))  _  _ = Refl
    trans (Int (Pred a)) (Int NegOne)   (Int NegOne)   _ ()
    trans (Int (Pred a)) (Int NegOne)   (Int (Pred c)) _ ()
    trans (Int (Pred a)) (Int (Pred b)) (Int Zero)     _  _ = Refl
    trans (Int (Pred a)) (Int (Pred b)) (Int One)      _  _ = Refl
    trans (Int (Pred a)) (Int (Pred b)) (Int (Suc c))  _  _ = Refl
    trans (Int (Pred a)) (Int (Pred b)) (Int NegOne)   _  _ = Refl
    trans (Int (Pred a)) (Int (Pred b)) (Int (Pred c)) lt1 lt2 = trans (Int a) (Int b) (Int c) lt1 lt2

negt : intType -> intType
negt Pos  = Neg
negt Neg  = Pos
negt Zero = Zero

neg : {t : intType} -> normalInt t -> normalInt (negt t)
neg Zero     = Zero
neg One      = NegOne
neg (Suc a)  = Pred (neg a)
neg NegOne   = One
neg (Pred a) = Suc (neg a)

suc : int -> int
suc (Int Zero)     = Int One
suc (Int One)      = Int (Suc One)
suc (Int (Suc a))  = Int (Suc (Suc a))
suc (Int NegOne)   = Int Zero
suc (Int (Pred a)) = Int a

pred : int -> int 
pred (Int Zero)     = Int NegOne
pred (Int One)      = Int Zero
pred (Int (Suc a))  = Int a
pred (Int NegOne)   = Int (Pred NegOne)
pred (Int (Pred a)) = Int (Pred (Pred a))

_plus_ : int -> int -> int
Int Zero     plus Int b        = Int b 
Int One      plus Int Zero     = Int One
Int One      plus Int One      = Int (Suc One)
Int One      plus Int (Suc b)  = Int (Suc (Suc b))
Int One      plus Int NegOne   = Int Zero
Int One      plus Int (Pred b) = Int b
Int (Suc a)  plus Int Zero     = Int (Suc a)
Int (Suc a)  plus Int One      = Int (Suc (Suc a))
Int (Suc a)  plus Int (Suc b)  = suc (suc (Int a plus Int b))
Int (Suc a)  plus Int NegOne   = Int a
Int (Suc a)  plus Int (Pred b) = Int a plus Int b
Int NegOne   plus Int Zero     = Int NegOne
Int NegOne   plus Int One      = Int Zero
Int NegOne   plus Int (Suc b)  = Int b
Int NegOne   plus Int NegOne   = Int (Pred NegOne)
Int NegOne   plus Int (Pred b) = Int (Pred (Pred b))
Int (Pred a) plus Int Zero     = Int (Pred a)
Int (Pred a) plus Int One      = Int a
Int (Pred a) plus Int (Suc b)  = Int a plus Int b
Int (Pred a) plus Int NegOne   = Int (Pred (Pred a))
Int (Pred a) plus Int (Pred b) = pred (pred (Int a plus Int b))

_minus_ : int -> int -> int
a minus Int b = a plus Int (neg b)

_times_ : int -> int -> int
Int Zero     times Int b = Int Zero
Int One      times Int b = Int b
Int (Suc a)  times Int b = (Int a times Int b) plus Int b
Int NegOne   times Int b = Int (neg b)
Int (Pred a) times Int b = (Int a times Int b) minus Int b

_div_ : int -> int -> int
a div b = b

