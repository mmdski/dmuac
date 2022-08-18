import Prelude hiding (Nothing, Maybe, Just)

-- Notes and exercises from Chapter 1

-- 1.1 Obtaining and Running Haskell
y = x+1
x = 4*5

-- 1.4.4 Function Definitions
square :: Integer -> Integer
square x = x*x

-- 1.4.5 Pattern Matching
-- f :: Integer -> String
-- f 1 = "one"
-- f 2 = "two"
-- f 3 = "three"

is_three :: Int -> Bool
is_three 3 = True
is_three x = False

nor :: Bool -> Bool -> Bool
nor False False = True
nor a     b     = False

isEmpty :: [a] -> Bool
isEmpty [] = True
isEmpty (x:xs) = False

-- Excercise 3
is_a :: Char -> Bool
is_a 'a' = True
is_a  x = False

-- Exercise 4
isHello :: String -> Bool
isHello "hello" = True
isHello x = False

-- Exercise 5
rmLeadingSpace :: [Char] -> [Char]
rmLeadingSpace (' ':xs) = xs
rmLeadingSpace (x:xs) = (x:xs)

-- 1.4.6 Higher Order Functions
twice :: (a->a) -> a -> a
twice f x = f (f x)

prod :: Integer -> Integer -> Integer
prod x y = x*y

g = prod 4
p = g 6
q = twice g 3

-- 1.6 Local Variabls: let Expressions

quadratic :: Double -> Double -> Double -> (Double,Double)
quadratic a b c
  = let d = sqrt (b^2 - 4*a*c)
        x1 = (-b + d) / (2*a)
        x2 = (-b - d) / (2*a)
       in (x1,x2)

-- 1.8 Common Functions on Lists
-- Exercise 6
intToBool :: Int -> Bool
intToBool 0 = False
intToBool 1 = True

convert :: [Int] -> [Bool]
convert x = map intToBool x

-- Excercise 7
isCharZero :: Char -> Bool
isCharZero '0' = True
isCharZero  a  = False

member0 :: String -> Bool
member0 x = or (map isCharZero x)

-- Exercise 8. Expand the following application:
-- foldr max 0 [1,5,3]
ex8 = max 0 (max 1 (max 5 3))

-- 1.9 Data Type Definitions
data Colour = Red | Orange | Yellow
        | Green | Blue | Violet deriving Show

data Animal a b = Cat a | Dog b | Rat
data BreedOfCat = Siamese | Persian | Moggie

data Maybe a = Nothing | Just a deriving Show

-- Exercise 9
addMaybeInt :: Maybe Integer -> Maybe Integer -> Maybe Integer
addMaybeInt Nothing Nothing = Nothing
addMaybeInt (Just x) Nothing = (Just x)
addMaybeInt Nothing (Just x) = (Just x)
addMaybeInt (Just x) (Just y) = (Just (x+y))
 
addJust :: [Maybe Integer] -> [Maybe Integer] -> [Maybe Integer]
addJust a b = zipWith addMaybeInt a b

-- Exercise 10
data Metal = Iron | Copper | Bronze | 
        Aluminium | Titanium | Zinc deriving (Eq, Show) 

-- Exercise 13
data UpToFourTuples a = OneTuple (a) | TwoTuple (a,a) | 
        ThreeTuple (a,a,a) | FourTuple (a,a,a,a) deriving (Eq,Show)

-- Exercise 14
data QuadraticResult = RealRoots (Double, Double) | 
        ComplexRoots deriving (Eq, Show)

quadraticReal :: Double -> Double -> Double -> QuadraticResult
quadraticReal a b c
  = let d = (b^2 - 4*a*c)
        res = if d < 0 then ComplexRoots else
                let x1 = (-b + sqrt d) / (2*a)
                    x2 = (-b - sqrt d) / (2*a)
                in RealRoots (x1,x2)
        in res

-- 1.10 Type Classes and Overloading
fun :: Eq b => Bool -> b -> b -> Bool
fun a b c = if a then b == c else False

detect :: (Eq a, Show a) => a -> [a] -> String
detect v list =
        if elem v list
           then "List contains " ++ show v
           else "List does not contain " ++ show v

-- 1.12 Review Excercises
-- Exercise 15
showMaybe :: Show a => Maybe a -> String
showMaybe b = (show b)

-- Exercise 16
bitOr :: Int -> Int -> Int
bitOr 0 0 = 0
bitOr x y = 1

bitAnd :: Int -> Int -> Int
bitAnd 1 1 = 1
bitAnd x y = 0

bitwiseAnd :: [Int] -> [Int] -> [Int]
bitwiseAnd x y = zipWith bitAnd x y

-- Exercise 20
justConstArg :: Maybe a-> a
justConstArg (Just a) = a

isJust :: Maybe a -> Bool
isJust (Just a) = True
isJust Nothing = False

-- [justConstArg x | x <- [Just 3, Nothing, Just 4], isJust x] => [3,4]
ex20 = [justConstArg x | x <- [Just 3, Nothing, Just 4], isJust x]

-- Exercise 21
elemGtN :: [Int] -> Int -> [Int]
elemGtN lst n = [x | x <- lst, x > n]
-- elemGtN [1,2,3,4,5] 3 => [4,5]

-- Exercise 22
f :: [Int] -> Int -> [Int]
f lst e = [i | (x,i) <- zip lst [0..(length lst)], x == e]

-- Exercise 23
ex23 = [floor x | x <- [1..20], floor (sqrt x)^2 /= floor x]

-- Exercise 24
countChar :: Char -> String -> Int
countChar c str = foldr (+) 0 [1 | a <- str, a == c]

-- Exercise 25
removeChar :: Char -> [Char] -> [Char]
removeChar c lst = foldr (:) [] [a | a <- lst, a /= c]

-- Exercise 26
rev :: [a] -> [a]
rev lst = foldl (flip (:)) [] lst

-- Exercise 27
nextMaybe :: Maybe a -> a -> Maybe a
nextMaybe x y = Just y

maybeLast :: [a] -> Maybe a
maybeLast [] = Nothing
maybeLast lst = 
        let first_elem = lst !! 0
            remain_lst = drop 0 lst
        in foldl nextMaybe (Just first_elem) remain_lst
