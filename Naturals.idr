import Prelude.Num

data MyNat = Zero' | Succ' MyNat

total 
MyNatAdd : MyNat -> MyNat -> MyNat
MyNatAdd Zero' m = m
MyNatAdd (Succ' m) n = Succ' (MyNatAdd m n)

total 
our_first_proof : (a : MyNat) -> MyNatAdd Zero' a = a
our_first_proof a = Refl

total
our_second_proof : (m : MyNat) -> DPair MyNat (\m => MyNat)
our_second_proof m = MkDPair m (Succ' m)


{-

Note that below code does not type check it requires a lambda in type 
declaration not a function type.

myDPair : String -> DPair String (String -> Nat)
myDPair s = MkDPair s (length s)

-}


myDPair : String -> DPair String (\_ => Nat)
myDPair s = MkDPair s (length s)


total proof_nat_exists : MyNat
proof_nat_exists = Zero'


-- This is also a proof that MyNat exists.
the_proof : MyNat
the_proof = the MyNat Zero'

total 
even : Nat -> Bool
even Z = True
even (S x) = not (even x)


data Even : Nat -> Type where
  Mkeven : (k : Nat) -> Even k

data Odd : Nat -> Type where
  MkOdd : (k : Nat) -> Odd k

-- it returns whether the given nat is even or odd and 
-- the corresponding proof.
even_or_odd : (k : Nat) -> Either (Even k) (Odd k)
even_or_odd k = if (even k) then Left (Mkeven k)
                            else Right (MkOdd k) 

