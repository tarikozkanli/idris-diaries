module Bridge

import Data.List

import Data.Subset


data Suit = Spade | Heart | Diamond | Club

data HighLabel = A | K | D | J

LowLabelIndex : Type
LowLabelIndex = Subset Nat $ Is (\x => x >= 2 && x <= 10) 

data LowLabel = Low LowLabelIndex

-- c1 : LowLabel
-- c1 = Low (refine 2)

Label = Either HighLabel LowLabel

data Card = ColorCard Suit Label

data SuitCards = Cards Suit (List Label)

Hand1 = List SuitCards

Hand2 = List Card 

-- example hands

hand1 : Hand1
hand1 = [Cards Spade [Left A, Left K, Right (Low (refine 5)), Right (Low (refine 3))],
         Cards Heart [Left D, Left J, Right (Low (refine 8)), Right (Low (refine 4)), Right (Low (refine 2))],
         Cards Diamond [Left A, Left J, Right (Low (refine 10))],
         Cards Club [Right (Low (refine 7))]
        ] 
