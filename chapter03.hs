import Prelude hiding ((!!), concat, foldr, last, lookup, map, zipWith)

-- Chapter 3: Recursion
factorial :: Int -> Int
factorial 0 = 1
factorial (n+1) = (n+1) * factorial n

-- 3.1 Recursion Over Lists

concat :: [[a]] -> [a]
concat [] = []
concat (xs:xss) = xs ++ concat xss

quicksort :: Ord a => [a] -> [a]
quicksort [] = []
quicksort (splitter:xs) =
        quicksort [y | y <- xs, y<splitter]
        ++ [splitter]
        ++ quicksort [y | y <- xs, y>=splitter]

-- Exercise 1
copy :: [a] -> [a]
copy [] = []
copy (x:xs) = x : copy xs
-- copy [2] => [2]

-- Exercise 2
inverse :: [(a,b)] -> [(b,a)]
inverse [] = []
inverse ((x,y):xs) = [(y,x)] ++ inverse xs
-- inverse [(1,2),(3,4)] ==> [(2,1),(4,3)]
 
-- Exercise 3
merge :: Ord a => [a] -> [a] -> [a]
merge [] y = y
merge x [] = x
merge (x:xs) (y:ys) 
  = if x < y 
       then [x] ++ merge xs (y:ys)
       else [y] ++ merge (x:xs) ys
-- merge [1,3,5] [2,4,6] ==> [1,2,3,4,5,6]
-- merge [4,5] [1,2,3]   ==> [1,2,3,4,5]
-- merge [3,4,5] [1,2]   ==> [1,2,3,4,5]

-- Exercise 4
(!!) :: [a] -> Int -> Maybe a
(!!) [] i = Nothing
(!!) (x:xs) i 
  = if i == 0 then Just x else (!!) xs (i-1)
-- [1,2,3]!!0 ==> Just 1
-- [1,2,3]!!2 ==> Just 3
-- [1,2,3]!!5 ==> Nothing

-- Exercise 5
lookup :: Eq a => a -> [(a,b)] -> Maybe b
lookup i [] = Nothing
lookup i ((x,y):xs) 
  = if i == x then (Just y) else (lookup) i xs
-- lookup 5 [(1,2),(5,3)] ==> Just 3
-- lookup 6 [(1,2),(5,3)] ==> Nothing

-- Exercise 6
count :: Eq a => a -> [a] -> Int
count x [] = 0
count x (y:ys) 
  = if x == y then 1 + count x ys else 0 + count x ys

-- Exercise 7
remove :: Eq a => a -> [a] -> [a]
remove x [] = []
remove x (y:ys) = let z = if x == y then [] else [y] in z ++ remove x ys
-- remove 1 [1,2,3,1,3] ==> [2,3,3]

-- Exercise 8
-- f :: [a] -> [a]
-- f [] = []
-- f [x] = []
-- f (x:xs:xss) = [xs] ++ f xss
-- f [1,2,3,4,5,6,7] ==> [2,4,6]

-- Exercise 9
extract :: [Maybe a] -> [a]
extract [] = []
extract ((Just x):xs) = [x] ++ extract xs
extract (Nothing:xs) = [] ++ extract xs
-- extract [Just 3, Nothing, Just 7] ==> [3,7]

-- Exercise 10
startsWith :: Eq a => [a] -> [a] -> Bool
startsWith []     [] = True
startsWith (x:xs) [] = True
startsWith []     (y:ys) = False
startsWith (x:xs) (y:ys) = if x == y then True && startsWith xs ys else False

strIn :: Eq a => Int -> [a] -> [a] -> Maybe Int
strIn i []     []     = Just i
strIn i []     (y:ys) = Nothing
strIn i (x:xs) []     = Just i
strIn i (x:xs) (y:ys) = if (startsWith (x:xs) (y:ys))
                           then Just i 
                           else strIn (i+1) xs (y:ys)

-- f :: String -> String -> Maybe Int
-- f str sstr = strIn 0 str sstr
-- f "abcde" "bc" ==> Just 1
-- f "abcde" "fg" ==> Nothing

-- 3.2 Higher Order Recursive Functions
map :: (a->b) -> [a] -> [b]
map f []     = []
map f (x:xs) = f x : map f xs

zipWith :: (a->b->c) -> [a] -> [b] -> [c]
zipWith f []     (y:ys) = []
zipWith f (x:xs) []     = []
zipWith f (x:xs) (y:ys) = f x y : zipWith f xs ys

foldr :: (a->b->b) -> b -> [a] -> b
foldr f z [] = z
foldr f z (x:xs) = f x (foldr f z xs)

sum :: Num a => [a] -> a
sum [] = 0
sum (x:xs) = foldr (+) x xs

firsts :: [(a,b)] -> [a]
firsts xs = map fst xs

-- Exercise 11
foldrWith :: (a->b->c->c) -> c -> [a] -> [b] -> c
foldrWith f z [] ys = z
foldrWith f z xs [] = z
foldrWith f z (x:xs) (y:ys) = f x y (foldrWith f z xs ys)
-- I don't really understand the application of this one

-- Exercise 12
-- mappend f xs = concat (map f xs)
mappend :: (a->[b]) -> [a] -> [b]
mappend f xs = foldr fun [] xs 
  where fun x acc = f x ++ acc -- where is defining a function here

-- Exercise 13
removeDuplicates :: Eq a => [a] -> [a]
removeDuplicates [] = []
-- removeDuplicates [x] = [x]
-- removeDuplicates (x:xs) = if foldr (||) False (map (==x) xs)
--                              then removeDuplicates xs
--                              else [x] ++ removeDuplicates xs
removeDuplicates (x:xs) =
        if elem x xs 
           then removeDuplicates xs
           else x : removeDuplicates xs

-- Exercise 14
member :: Eq a => a -> [a] -> Bool
member x [] = False
member x (y:ys) = if x == y then True else member x ys

-- 3.3 Peano Arithmitic

data Peano = Zero | Succ Peano deriving Show
-- 1 = Succ Zero
-- 3 = Succ (Succ (Succ Zero))

data List a = Empty | Cons a (List a)

decrement :: Peano -> Peano
decrement Zero     = Zero
decrement (Succ a) = a

add :: Peano -> Peano -> Peano
add Zero b     = b
add (Succ a) b = Succ (add a b)

sub :: Peano -> Peano -> Peano
sub a        Zero     = a
sub Zero     b        = Zero
sub (Succ a) (Succ b) = sub a b

equals :: Peano -> Peano -> Bool
equals Zero     Zero     = True
equals Zero     b        = False
equals a        Zero     = False
equals (Succ a) (Succ b) = equals a b

lt :: Peano -> Peano -> Bool
lt a        Zero     = False
lt Zero     (Succ b) = True
lt (Succ a) (Succ b) = lt a b

-- 3.4 Data Recursion
f :: a -> [a]
f x = x : f x

ones = f 1

twos = 2 : twos

-- 3.6 Review Exercises
-- Exercise 15
intersection :: Eq a => [a] -> [a] -> [a]
intersection [] [] = []
intersection xs [] = []
intersection [] ys = []
intersection (x:xs) ys = 
        if elem x ys then x : intersection xs ys else intersection xs ys

-- Exercise 16
isSubset :: Eq a => [a] -> [a] -> Bool
isSubset [] ys = True -- is the empty set a subset of all sets?
isSubset xs [] = False
isSubset (x:xs) ys =
        if elem x ys then True && isSubset xs ys else False

-- Exercise 17
isSorted :: Ord a => [a] -> Bool
isSorted [x] = True
isSorted (x1:x2:xs) = if x1 <= x2 then True && isSorted (x2:xs) else False

-- Exercise 18
-- factorial from previous section:
-- factorial :: Int -> Int
-- factorial 0 = 1
-- factorial (n+1) = (n+1) * factorial n
--
-- factorial n
-- = n * factorial n-1
-- = n * (n-1) * factorial n-2
-- = n * (n-1) * ... * factorial 2
-- = n * (n-1) * ... * 2 * factorial 1
-- = n * (n-1) * ... * 2 * 1 * factorial 0
-- = n * (n-1) * ... * 2 * 1 * 1
-- = n!
--
-- factorial n = foldr (*) 1 [1..n]
-- factorial n
-- = foldr (*) 1 [1..n]
-- = 1 * (foldr (*) 1 [2..n])
-- = 1 * 2 * (foldr (*) 1 [3..n])
-- = 1 * 2 * ... * (n-1) * (foldr (*) 1 [n])
-- = 1 * 2 * ... * (n-1) * n * (foldr (*) 1 [])
-- = 1 * 2 * ... * (n-1) * n * 1 
-- = n!
 
-- Exercise 19
last :: [a] -> Maybe a
last [] = Nothing
last [a] = Just a
last (x:xs) = last xs

-- Exercise 20
wholePart :: String -> String
wholePart "" = ""
wholePart ('.':ss) = ""
wholePart (s:ss) = s : wholePart ss
-- wholePart (s:ss) = if (s == '.') then "" else (s : wholePart ss)

fractionalPart :: String -> String
fractionalPart "" = ""
fractionalPart (s:'.':ss) = ss
fractionalPart (s:ss) = fractionalPart ss

-- wholePart "23.455" => "23"
-- fractionalPart "23.455" => "455"
