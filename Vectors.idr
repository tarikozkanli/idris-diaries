import Data.Vect

fourInts : Vect 4 Int
fourInts = [0, 1, 2, 3]

sixInts : Vect 6 Int
sixInts = [4, 5, 6, 7, 8, 9]

tenInts : Vect 10 Int
tenInts = fourInts ++ sixInts
WordLength_vec.idr

multMatrix : Num numType =>
Vect n (Vect m numType) -> Vect m (Vect p numType) -> Vect n (Vect p numType)
