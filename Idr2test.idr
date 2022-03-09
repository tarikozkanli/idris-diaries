module Idr2test

import Data.Vect

data Bin : Type where
  On  : Bin
  Off : Bin

fact :  Int -> Int
fact 0 = 1
fact n = n * fact (n-1)

append : Vect n a -> Vect m a -> Vect (n+m) a
append [] ys = ys
append (x :: xs) ys = x :: append xs ys


fact_0 : fact 0 = 1
fact_0 = Refl

data MyVect : (n : Nat) -> Type where
  Empty : MyVect 0
  Cons  : (x : Nat) -> (xs : MyVect len) -> MyVect (S len)

x : MyVect 2
x = Cons 1 (Cons 2 Empty)

y : MyVect 3
y = Cons 1 (Cons 2 (Cons 3 Empty))


isSingleton : Bool -> Type
isSingleton False = MyVect 0 
isSingleton True = Nat 

mkSingle : (x : Bool) -> isSingleton x
mkSingle False = Empty
mkSingle True = 0

lengthMyVect : {n: Nat} -> MyVect n -> Nat
lengthMyVect {n = k} _ = k


ifthenelse : Bool -> Lazy a -> Lazy a -> a
ifthenelse False t e = e
ifthenelse True t e = t

laz : Lazy Int
laz = 3 + 4 -- Delay (3 + 4)
kaz = Force laz -- 7

the' : (a : Type) -> a -> a 
the' x y = y

data Or a b = Or_introl a | Or_intror b

proof_1 : a -> Or a b
proof_1 a = Or_introl a

proof_2 : b -> Or a b
proof_2 b = Or_intror b


data Weekday = Mon | Tue | Wed | Thu | Fri | Sat | Sun

total
next_day : Weekday -> Weekday
next_day Mon = Tue
next_day Tue = Wed 
next_day Wed = Thu
next_day Thu = Fri
next_day Fri = Sat
next_day Sat = Sun
next_day Sun = Mon

total
prev_day : Weekday -> Weekday
prev_day Mon = Sun 
prev_day Tue = Mon
prev_day Wed = Tue
prev_day Thu = Wed
prev_day Fri = Thu
prev_day Sat = Fri
prev_day Sun = Sat


week_day_prf_1 : next_day Mon = Tue
week_day_prf_1 = Refl

week_day_prf_2 : prev_day Mon = Sun
week_day_prf_2 = Refl

is_it_monday : Weekday -> Bool
is_it_monday Mon = True 
is_it_monday _   = False

proof_is_it_monday : (day : Weekday) -> day = Mon 
                     -> is_it_monday day = True
proof_is_it_monday day day_eq_mon 
    = rewrite day_eq_mon in Refl 

is_it_sunday : Weekday -> Bool
is_it_sunday Sun = True
is_it_sunday _   = False

proof_is_it_sunday : (day : Weekday) -> day = Sun
                     -> is_it_sunday day = True
proof_is_it_sunday day day_eq_sunday 
    = rewrite day_eq_sunday in Refl

proof_mon_is_tue : is_it_monday Tue = True -> Void
proof_mon_is_tue Refl impossible

data Void' : Type


proof_mon_is_tue' : is_it_monday Tue = True -> Void'
proof_mon_is_tue' Refl impossible


one_eq_two : 1 = 2 -> Void'
one_eq_two Refl impossible

{-

An equality type for Types.
ex:  Nat = Nat , Bool = Bool

-}

idType: (a : Type) -> a = a
idType type = Refl




