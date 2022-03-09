

data MyNat = Zero | Succ MyNat

total 
MyNatAdd : MyNat -> MyNat -> MyNat
MyNatAdd Zero m = m
MyNatAdd (Succ m) n = Succ (MyNatAdd m n)

total 
our_first_proof : (a : MyNat) -> MyNatAdd Zero a = a
our_first_proof a = Refl

total
our_second_proof : (m : MyNat) -> DPair MyNat (\m => MyNat)
our_second_proof m = MkDPair m (Succ m)


{-

Note that below code does not type check it requires a lambda in type 
declaration not a function type.

myDPair : String -> DPair String (String -> Nat)
myDPair s = MkDPair s (length s)

-}


myDPair : String -> DPair String (\_ => Nat)
myDPair s = MkDPair s (length s)

