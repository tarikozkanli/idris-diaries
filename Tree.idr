

-- Binary tree data type.
data Tree elem = Empty
                | Node (Tree elem) elem (Tree elem)

-- Name templates for variables.
%name Tree tree, tree1

-- Binary Tree insertion.
insert : Ord elem => elem -> Tree elem -> Tree elem
insert x Empty = Node Empty x Empty
insert x (Node left val right) = case (compare x val) of
                                    LT => Node (insert x left) val right
                                    EQ => Node  left val right
                                    GT => Node left val (insert x right)


listToTree : Ord a => List a -> Tree a
listToTree [] = Empty
listToTree (x :: xs) = insert x (listToTree xs)

treeToList : Tree a -> List a
treeToList Empty = []
treeToList (Node left val right) =
                      (treeToList left) ++
                      [val] ++
                      (treeToList right)
data Expr = Val Int
           | Add Expr Expr
           | Mult Expr Expr
           | Subtr Expr Expr

evaluate : Expr -> Int
evaluate (Val x)     = x
evaluate (Add x y)   = (evaluate x) + (evaluate y)
evaluate (Mult x y)  = (evaluate x) * (evaluate y)
evaluate (Subtr x y) = (evaluate x) - (evaluate y)

maxMaybe : Ord a => Maybe a -> Maybe a -> Maybe a
maxMaybe Nothing Nothing = Nothing
maxMaybe Nothing _ = Just x
maxMaybe (Just x) Nothing = Just x
maxMaybe (Just x) (Just y) = Just (max x y)
