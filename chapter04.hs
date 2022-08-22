import Prelude hiding ((.), (++), concat, foldr, map, length, sum)
import Char
-- Chapter 4: Induction
--
-- 4.2 Examples of Induction on Natural Numbers
-- Exercise 1
-- Let a be an arbitrary real number. Prove, for all natural numbers m and n,
-- that a^(m*n) = (a^m)^n
--
-- P(m,n) = (a^(m*n) = (a^m)^n)
-- 
-- Using x^0 = 1 and x*x^n = x^(n+1)
--
-- Base cases:
-- Prove P(0,n):
--      a^(0*n) = (a^0)^n -> a^0 = 1^n -> 1 = 1
-- Prove P(m,0):
--      a^(m*0) = (a^m)^0 -> a^0 = 1 -> 1 = 1
-- Therefore, P(0,n) and P(m,0)
--
-- Induction cases:
-- Prove P(m,n) -> P(m+1,n)
-- a^((m+1)*n) = a^(m*n+n)
--      = a^(m*n)*a^n
--      = (a^m)^n*a^n -- a^(m*n) -> (a^m)^n from induction hypothesis
--      = (a^m*a)^n
--      = (a^(m+1))^n
-- P(m,n) -> P(m+1,n)
--
-- Prove P(m,n) -> P(m,n+1)
-- a^(m*(n+1)) = a^(m*n+m)
--      = a^(m*n)*a^m
--      = (a^m)^n*a^m
--      = (a^m)^(n+1)
-- P(m,n) -> P(m,n+1)
--
-- Exercise 2
-- Prove that the sum of the first n odd positive numbers is n^2.
--
-- Define odd numbers by 2*n+1 for n = 0 ...
-- P(n) = sum (2*i+1)^2 from 0 to n = n^2
--
-- Base case:
-- P(0) = sum 2*i+1 from 0 to 1 = 1^2
--      = 2*0 + 1 = 1^2
--      = 1 = 1
-- Therefore, P(0).
--
-- Inductive case:
-- P(n) = sum 2*i-1 from 0 to n = n^2
-- P(n+1) = sum 2*i-1 from 0 to n+1
--      = sum 2*i-1 from 0 to n + 2*(n+1)-1
--      = n^2 + 2n + 1
--      = (n+1)^2
-- P(n) -> P(n+1)
--
-- Exercise 3
-- I believe the book is incorrect and the series should start at i=0.
-- Prove that sum a^i from i=0 to n = (a^(n+1)-1)/(a-1), where a is a real
--      number and a /= 1.
--
-- P(0) = 1 = (a^(0+1)-1)/(a-1) 
--      = (a-1)/(a-1) 
--      = 1
-- Therefore, P(0).
--
-- Inductive case:
-- P(n) = sum a^i from i=0 to n = (a^(n+1)-1)/(a-1)
-- P(n+1) = sum a^i from i=0 to n+1 = sum a^i from i=0 to n + a^(n+1)
--      = (a^(n+1)-1)/(a-1) + a^(n+1)
--      = ((a^(n+1)-1) + a^(n+1)(a-1))/(a-1)
--      = (a^(n+1)-1 + a^(n+2)-a^(n+1))/(a-1)
--      = (a^(n+2)-1)/(a-1)
-- P(n) -> P(n+1)
--
-- 4.3 Induction and Recursion
-- Exercise 4
--
fib :: Integer -> Integer
fib 0 = 0
fib 1 = 1
fib (n+2) = fib n + fib (n+1)
-- Prove sum fib i from i to n = (fib n+2) - 1
-- 
-- Base case: P(0)
-- P(0) = sum fib 0 from 1 to 0 = (fib n+2) - 1
--      0 = (fib 0+2) - 1 = 1 - 1 = 0
-- Therefore, P(0)
--
-- Inductive case: P(n) -> P(n+1)
-- P(n) = sum fib i from 1 to n = (fib n+2) - 1
-- P(n+1) = sum fib i from 1 to n+1 = (fib n+3) - 1
--
-- (fib n+3) - 1 
--      = (fib n+1 + fib n+2) - 1               {fib.3}
--      = (fib n+2) - 1 + fib n+1
--      = sum fib i from 1 to n + fib n+1       {hypothesis}
--      = sum fib i from 1 to n+1               {def. sum}
-- P(n) -> P(n+1)

-- 4.5 Induction on Lists
(++) :: [a] -> [a] -> [a]
(++) [] ys = ys
(++) (x:xs) ys = x : (xs++ys)

sum :: Num a => [a] -> a
sum [] = 0
sum (x:xs) = x + sum xs

-- Theorem 15. sum (xs++ys) = sum xs + sum ys
-- Proof. Induction over xs. The base case is
--
-- sum ([] ++ ys)
--      = sum ys                { (++).1 }
--      = 0 + sum ys            { 0 + x = x }
--      = sum [] + sum ys       { sum.1 }
--
-- The inductive case is
--
-- sum ((x:xs)++ys)
--      = sum (x : (xs++ys))    { (++).2 }
--      = x + sum (xs++ys)      { sum.2 }
--      = x + sum xs + sum ys   { hypothesis }
--      = sum (x:xs) + sum ys   { sum.2 }
--
length :: [a] -> Int
length [] = 0
length (x:xs) = 1 + length xs
-- Theorem 16. length (xs++ys) = length xs + length ys
-- (left as an exercise)
--
map :: (a->b) -> [a] -> [b]
map f []     = []
map f (x:xs) = f x : map f xs
--
-- Theorem 17. length (map f xs) = length xs
--
-- Proof. Induction over xs. The base case is
--
-- length (map f [])
--      = length []     { map.1 }
--
-- Inductive case: assume length (map f xs) = length xs
--
-- length (map f (x:xs))
--      = length (f x : map f xs)       { map.2 }
--      = 1 + length (map f xs)         { length.2 }
--      = 1 + length xs                 { hypothesis }
--      = length (x:xs)                 { length.2 }
--
-- Theorem 18. map f (xs++ys) = map f xs ++ map f ys
-- (left as an exercise)
--
-- Theorem 19. (map f . map g) xs = map (f.g) xs
-- (left as an exercise)
-- 
-- Theorem 20. sum (map (1+) xs) = length xs + sum xs
--
-- Proof. Induction over xs. The base case is
--
-- sum (map (1+) [])
--      = sum []                { map.1 }
--      = 0 + sum []            { 0 + x = x }
--      = length [] + sum []    { length.1 }
--
-- Inductive case. Assume sum (map (1+) xs) = length xs + sum xs
-- sum (map (+1) (x:xs))
--      = sum ((1 + x) : map (1+) xs)           { map.2 }
--      = (1 + x) + sum (map (1+) xs)           { sum.2 }
--      = (1 + x) + (length xs + sum xs)        { hypothesis }
--      = (1 + length xs) + (x + sum xs)        { (+).algebra }
--      = length (x:xs) + sum (x:xs)            { length.2, sum.2}
--
foldr :: (a->b->b) -> b -> [a] -> b
foldr f z [] = z
foldr f z (x:xs) = f x (foldr f z xs)
-- 
-- Theorem 21. foldr (:) [] xs = xs
--
-- Proof. Induction over xs. The base case is
--
-- foldr (:) [] []
--      = []                    { foldr.1 }
--
-- Inductive case. Assume foldr (:) [] xs = xs.
--
-- foldr (:) [] (x:xs)
--      = x : foldr (:) [] xs   { foldr.2 }
--      = x:xs                  { hypothesis }
--
concat :: [[a]] -> [a]
concat [] = []
concat (xs:xss) = xs ++ concat xss
--
-- Theorem 22. map f (concat xss) = concat (map (map f) xss)
--
-- Proof. Induction over xs. The base case is
--
-- map f (concat [])
--      = map f []                      { concat.1 }
--      = []                            { map.1 }
--      = concat []                     { concat.1 }
--      = concat (map f [] )            { map.1 }
--      = concat (map (map f) [] )      { map.1 }
--
-- Inductive case. Assume map f (concat xss) = concat (map (map f) xss)
--
-- map f (concat (xs:xss))
--      = map f (xs ++ concat xss)              { concat.2 }
--      = map f xs ++ map f (concat xss)        { Theorem 18 }
--      = map f xs ++ concat (map (map f) xss)  { hypothesis }
--      = concat(map f xs : map (map f) xss)    { concat.2 }
--      = concat(map (map f) (xs:xss))          { map.2 }
--
-- Theorem 23. length (xs ++ (y:ys)) = 1 + length xs + length ys
--
-- length (xs ++ (y:ys))
--      = length xs + length (y:ys)
--      = length xs + (1 + length ys)
--      = 1 + length xs + length ys
-- 
-- Exercise 5. Prove theorem 16
-- Theorem 16. length (xs++ys) = length xs + length ys
--
-- Proof. Induction over xs. The base case is
--
-- length ([]++ys)
--      = length ys                     { (++).1 }
--      = 0 + length ys                 { 0 + x = x }
--      = length [] + length ys         { length.1 }
-- 
-- Inductive case. Assume length (xs++ys) = length xs + length ys.
--
-- length ((x:xs)++ys) =
--      = length (x : (xs++ys))         { (++).2 }
--      = 1 + length (xs++ys)           { length.2 }
--      = 1 + length xs + length ys     { hypothesis }
--      = length (x:xs) + length ys     { length.2 }
--
-- QED
--
-- Exercise 6. Prove theorem 18.
-- Theorem 18. map f (xs++ys) = map f xs ++ map f ys
--
-- Proof. Induction over xs. The base case is
--
-- map f ([]++ys)
--      = map f ys                      { (++).1 }
--      = [] ++ map f ys                { (++).1 }
--      = map f [] ++ map f ys          { map.1 }

-- Inductive case. Assume map f (xs++ys) = map f xs ++ map f ys
--
-- map f ((x:xs)++ys)
--      = map f (x : (xs++ys))          { (++).2 }
--      = f x : map f (xs++ys)          { map.2 }
--      = f x : (map f xs ++ map f ys)  { hypothesis }
--      = (f x : map f xs) ++ map f ys  { (++).2 }
--      = map f (x:xs) ++ map f ys      { map.2 }
--
-- QED
--
-- Exercise 7. Prove theorem 19.
(.) :: (a -> b) -> (c -> a) -> c -> b
(.) f g x = f (g x)
-- Theorem 19. (map f . map g) xs = map (f.g) xs
--
-- Proof. The base case is
--
-- (map f . map g) []
--      = map f (map g [])              { (.) }
--      = map f []                      { map.1 }
--      = []                            { map.1 }
--      = map (f.g) []                  { map.1 }
--
-- By induction over xs. Assume (map f . map g) xs = map (f.g) xs
--
-- (map f . map g) (x:xs)
--      = map f (map g (x:xs))          { (.) }
--      = map f (g x : map g xs)        { map.2 }
--      = f (g x) : map f (map g xs)    { map.2 }
--      = f.g x : (map f . map g) xs    { (.) }
--      = f.g x : map (f.g) xs          { hypothesis }
--      = map (f.g) (x:xs)              { map.2 }
