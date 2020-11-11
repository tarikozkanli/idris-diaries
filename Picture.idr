

||| Represents shapes
data Shape = ||| A triangle, with its base length and height
            Triangle Double Double
          |  ||| A rectangle, with its length and height
           Rectangle Double Double
          |  ||| A circle, with its radius
           Circle Double

area : Shape -> Double
area (Triangle base height)    = 0.5 * base * height
area (Rectangle length height) = length * height
area (Circle radius)           = pi * radius * radius

data Picture = Primitive Shape
            | Combine Picture Picture
            | Rotate Double Picture
            | Translate Double Double Picture

rectangle : Picture
rectangle = Primitive (Rectangle 20 10)

circle : Picture
circle = Primitive (Circle 5)

triangle : Picture
triangle = Primitive (Triangle 10 10)

testPicture : Picture
testPicture = Combine (Translate 5 5 rectangle)
                      (Combine (Translate 35 5 circle)
                               (Translate 15 25 triangle))

pictureArea : Picture -> Double
pictureArea (Primitive x) = area x
pictureArea (Combine x y) = (pictureArea x) + (pictureArea y)
pictureArea (Rotate x y) = pictureArea y
pictureArea (Translate x y z) = pictureArea z


testPic1 : Picture
testPic1 = Combine (Primitive (Triangle 2 3))
                  (Primitive (Triangle 2 4))
testPic2 : Picture
testPic2 = Combine (Primitive (Rectangle 1 3))
                   (Primitive (Circle 4))

biggestTriangle : Picture -> Maybe Double
biggestTriangle (Primitive (Triangle x y)) = Just (area (Triangle x y))
biggestTriangle (Primitive _) = Nothing
biggestTriangle (Rotate x y) = biggestTriangle y
biggestTriangle (Translate x y z) = biggestTriangle z
biggestTriangle (Combine x y) = max (biggestTriangle x) (biggestTriangle y)

data DivResult = DivByZero | Result Double

safeDivide : Double -> Double -> Maybe Double
safeDivide x y = if y == 0 then Nothing
                  else Just (x / y)
