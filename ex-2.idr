palindrome : (n : Nat) -> (s: String) -> Bool
palindrome n s = (toLower s) == reverse (toLower s) && (length s) > n

total
counts : String -> (Nat, Nat)
counts s = (length (words s), length s)

showCounts : String -> String
showCounts s = "(# of words, # of chars) : " ++ show (counts s) ++ "\n"

top_ten : Ord a => List a -> List a
top_ten lst = take 10 (reverse (sort lst))

over_length : Nat -> List String -> Nat
--over_length n ss = length (filter (>3) (map length ss))
--without parens and using $ :~ apply
over_length n ss = length $ filter (> n) $ map length $ ss

main : IO ()
main = repl "Enter your string of interest : "
        showCounts
