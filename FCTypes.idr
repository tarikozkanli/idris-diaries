StringOrInt : Bool -> Type
StringOrInt x = case x of
                  True => Int
                  False => String

getStringOrInt : (x : Bool) -> StringOrInt x
getStringOrInt x = case x of
                     True => 94
                     False => "Ninety four"

valToString : (x : Bool) -> StringOrInt x -> String
valToString x val = case x of
                      True => cast val
                      False => val

-- Constraining ty type variable
double : Num ty => ty -> ty
double x = x + x

-- higher order function
twice : (a -> a) -> a -> a
twice f x = f (f x)

quadruple : Num a => a -> a
quadruple = twice double

Shape : Type
-- data Shape = Triangle | Rectangle | Circle
Shape = (String, Int)


rotate : Shape -> Shape


turn_around : Shape -> Shape
turn_around = twice rotate


longer : String -> String -> Nat
longer word1 word2
              = let len1 = length word1
                    len2 = length word2
                    in
                if len1 > len2 then len1 else len2


pythagoras : Double -> Double -> Double
pythagoras x y = sqrt (square x + square y)
                  where
                    square : Double -> Double
                    square x = x * x

wordCount : String -> Nat
wordCount str = length (words str)

allLengths : List String -> List Nat
allLengths strs = map length strs
