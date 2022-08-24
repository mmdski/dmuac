>import Prelude hiding ((.), (++), and, concat, foldr, length, map, 
>       maximum, or, reverse, sum)
>import Char

Chapter 4: Induction

4.2 Examples of Induction on Natural Numbers
Exercise 1
Let a be an arbitrary real number. Prove, for all natural numbers m and n,
that a^(m*n) = (a^m)^n

P(m,n) = (a^(m*n) = (a^m)^n)

Using x^0 = 1 and x*x^n = x^(n+1)

Base cases:
Prove P(0,n):
     a^(0*n) = (a^0)^n -> a^0 = 1^n -> 1 = 1
Prove P(m,0):
     a^(m*0) = (a^m)^0 -> a^0 = 1 -> 1 = 1
Therefore, P(0,n) and P(m,0)

Induction cases:
Prove P(m,n) -> P(m+1,n)
a^((m+1)*n) = a^(m*n+n)
     = a^(m*n)*a^n
     = (a^m)^n*a^n a^(m*n) -> (a^m)^n from induction hypothesis
     = (a^m*a)^n
     = (a^(m+1))^n
P(m,n) -> P(m+1,n)

Prove P(m,n) -> P(m,n+1)
a^(m*(n+1)) = a^(m*n+m)
     = a^(m*n)*a^m
     = (a^m)^n*a^m
     = (a^m)^(n+1)
P(m,n) -> P(m,n+1)

Exercise 2
Prove that the sum of the first n odd positive numbers is n^2.

Define odd numbers by 2*n+1 for n = 0 ...
P(n) = sum (2*i+1)^2 from 0 to n = n^2

Base case:
P(0) = sum 2*i+1 from 0 to 1 = 1^2
     = 2*0 + 1 = 1^2
     = 1 = 1
Therefore, P(0).

Inductive case:
P(n) = sum 2*i-1 from 0 to n = n^2
P(n+1) = sum 2*i-1 from 0 to n+1
     = sum 2*i-1 from 0 to n + 2*(n+1)-1
     = n^2 + 2n + 1
     = (n+1)^2
P(n) -> P(n+1)

Exercise 3
I believe the book is incorrect and the series should start at i=0.
Prove that sum a^i from i=0 to n = (a^(n+1)-1)/(a-1), where a is a real
     number and a /= 1.

P(0) = 1 = (a^(0+1)-1)/(a-1) 
     = (a-1)/(a-1) 
     = 1
Therefore, P(0).

Inductive case:
P(n) = sum a^i from i=0 to n = (a^(n+1)-1)/(a-1)
P(n+1) = sum a^i from i=0 to n+1 = sum a^i from i=0 to n + a^(n+1)
     = (a^(n+1)-1)/(a-1) + a^(n+1)
     = ((a^(n+1)-1) + a^(n+1)(a-1))/(a-1)
     = (a^(n+1)-1 + a^(n+2)-a^(n+1))/(a-1)
     = (a^(n+2)-1)/(a-1)
P(n) -> P(n+1)

4.3 Induction and Recursion
Exercise 4

>fib :: Integer -> Integer
>fib 0 = 0
>fib 1 = 1
>fib (n+2) = fib n + fib (n+1)

Prove sum fib i from i to n = (fib n+2) - 1

Base case: P(0)
P(0) = sum fib 0 from 1 to 0 = (fib n+2) - 1
     0 = (fib 0+2) - 1 = 1 - 1 = 0
Therefore, P(0)

Inductive case: P(n) -> P(n+1)
P(n) = sum fib i from 1 to n = (fib n+2) - 1
P(n+1) = sum fib i from 1 to n+1 = (fib n+3) - 1

(fib n+3) - 1 
     = (fib n+1 + fib n+2) - 1               {fib.3}
     = (fib n+2) - 1 + fib n+1
     = sum fib i from 1 to n + fib n+1       {hypothesis}
     = sum fib i from 1 to n+1               {def. sum}
P(n) -> P(n+1)

4.5 Induction on Lists

>(++) :: [a] -> [a] -> [a]
>(++) [] ys = ys
>(++) (x:xs) ys = x : (xs++ys)

>sum :: Num a => [a] -> a
>sum [] = 0
>sum (x:xs) = x + sum xs

Theorem 15. sum (xs++ys) = sum xs + sum ys
Proof. Induction over xs. The base case is

sum ([] ++ ys)
     = sum ys                { (++).1 }
     = 0 + sum ys            { 0 + x = x }
     = sum [] + sum ys       { sum.1 }

The inductive case is

sum ((x:xs)++ys)
     = sum (x : (xs++ys))    { (++).2 }
     = x + sum (xs++ys)      { sum.2 }
     = x + sum xs + sum ys   { hypothesis }
     = sum (x:xs) + sum ys   { sum.2 }

>length :: [a] -> Int
>length [] = 0
>length (x:xs) = 1 + length xs

Theorem 16. length (xs++ys) = length xs + length ys
(left as an exercise)

>map :: (a->b) -> [a] -> [b]
>map f []     = []
>map f (x:xs) = f x : map f xs

Theorem 17. length (map f xs) = length xs

Proof. Induction over xs. The base case is

length (map f [])
     = length []     { map.1 }

Inductive case: assume length (map f xs) = length xs

length (map f (x:xs))
     = length (f x : map f xs)       { map.2 }
     = 1 + length (map f xs)         { length.2 }
     = 1 + length xs                 { hypothesis }
     = length (x:xs)                 { length.2 }

Theorem 18. map f (xs++ys) = map f xs ++ map f ys
(left as an exercise)

Theorem 19. (map f . map g) xs = map (f.g) xs
(left as an exercise)

Theorem 20. sum (map (1+) xs) = length xs + sum xs

Proof. Induction over xs. The base case is

sum (map (1+) [])
     = sum []                { map.1 }
     = 0 + sum []            { 0 + x = x }
     = length [] + sum []    { length.1 }

Inductive case. Assume sum (map (1+) xs) = length xs + sum xs
sum (map (+1) (x:xs))
     = sum ((1 + x) : map (1+) xs)           { map.2 }
     = (1 + x) + sum (map (1+) xs)           { sum.2 }
     = (1 + x) + (length xs + sum xs)        { hypothesis }
     = (1 + length xs) + (x + sum xs)        { (+).algebra }
     = length (x:xs) + sum (x:xs)            { length.2, sum.2}

>foldr :: (a->b->b) -> b -> [a] -> b
>foldr f z [] = z
>foldr f z (x:xs) = f x (foldr f z xs)

Theorem 21. foldr (:) [] xs = xs

Proof. Induction over xs. The base case is

foldr (:) [] []
     = []                    { foldr.1 }

Inductive case. Assume foldr (:) [] xs = xs.

foldr (:) [] (x:xs)
     = x : foldr (:) [] xs   { foldr.2 }
     = x:xs                  { hypothesis }

>concat :: [[a]] -> [a]
>concat [] = []
>concat (xs:xss) = xs ++ concat xss

Theorem 22. map f (concat xss) = concat (map (map f) xss)

Proof. Induction over xs. The base case is

map f (concat [])
     = map f []                      { concat.1 }
     = []                            { map.1 }
     = concat []                     { concat.1 }
     = concat (map f [] )            { map.1 }
     = concat (map (map f) [] )      { map.1 }

Inductive case. Assume map f (concat xss) = concat (map (map f) xss)

map f (concat (xs:xss))
     = map f (xs ++ concat xss)              { concat.2 }
     = map f xs ++ map f (concat xss)        { Theorem 18 }
     = map f xs ++ concat (map (map f) xss)  { hypothesis }
     = concat(map f xs : map (map f) xss)    { concat.2 }
     = concat(map (map f) (xs:xss))          { map.2 }

Theorem 23. length (xs ++ (y:ys)) = 1 + length xs + length ys

length (xs ++ (y:ys))
     = length xs + length (y:ys)
     = length xs + (1 + length ys)
     = 1 + length xs + length ys

Exercise 5. Prove theorem 16
Theorem 16. length (xs++ys) = length xs + length ys

Proof. Induction over xs. The base case is

length ([]++ys)
     = length ys                     { (++).1 }
     = 0 + length ys                 { 0 + x = x }
     = length [] + length ys         { length.1 }

Inductive case. Assume length (xs++ys) = length xs + length ys.

length ((x:xs)++ys) =
     = length (x : (xs++ys))         { (++).2 }
     = 1 + length (xs++ys)           { length.2 }
     = 1 + length xs + length ys     { hypothesis }
     = length (x:xs) + length ys     { length.2 }

QED

Exercise 6. Prove theorem 18.
Theorem 18. map f (xs++ys) = map f xs ++ map f ys

Proof. Induction over xs. The base case is

map f ([]++ys)
     = map f ys                      { (++).1 }
     = [] ++ map f ys                { (++).1 }
     = map f [] ++ map f ys          { map.1 }

Inductive case. Assume map f (xs++ys) = map f xs ++ map f ys

map f ((x:xs)++ys)
     = map f (x : (xs++ys))          { (++).2 }
     = f x : map f (xs++ys)          { map.2 }
     = f x : (map f xs ++ map f ys)  { hypothesis }
     = (f x : map f xs) ++ map f ys  { (++).2 }
     = map f (x:xs) ++ map f ys      { map.2 }

QED

Exercise 7. Prove theorem 19.

>(.) :: (a -> b) -> (c -> a) -> c -> b
>(.) f g x = f (g x)

Theorem 19. (map f . map g) xs = map (f.g) xs

Proof. The base case is

(map f . map g) []
     = map f (map g [])              { (.) }
     = map f []                      { map.1 }
     = []                            { map.1 }
     = map (f.g) []                  { map.1 }

By induction over xs. Assume (map f . map g) xs = map (f.g) xs

(map f . map g) (x:xs)
     = map f (map g (x:xs))          { (.) }
     = map f (g x : map g xs)        { map.2 }
     = f (g x) : map f (map g xs)    { map.2 }
     = f.g x : (map f . map g) xs    { (.) }
     = f.g x : map (f.g) xs          { hypothesis }
     = map (f.g) (x:xs)              { map.2 }

Exercise 8. sum (map (1+) xs) = length xs + sum xs

After adding one to each element in a list xs, the sum of all elements in
the list is equal to the length of the list plus 

The sum of all incremented elements in a list xs is equal the length of xs
plus the sum of all elements in xs.

xs = [1,2,3,4]
sum (map (1+) [1,2,3,4] )
     = sum (1+1 : map (1+) [2,3,4] )
     = sum ( 1+1 : 1+2 : map (1+) [3,4] )
     = sum ( 1+1 : 1+2 : 1+3 : map (1+) [4] )
     = sum ( 1+1 : 1+2 : 1+3 : 1+4 : map (1+) [] )
     = sum ( 1+1 : 1+2 : 1+3 : 1+4 : [] )
     = sum ( 2 : 3 : 4 : 5 : [] )
     = sum ( 2 : 3 : 4 : [5] )
     = sum ( 2 : 3 : [4,5] )
     = sum ( 2 : [3,4,5] )
     = sum [2,3,4,5]
     = 2 + sum [3,4,5]
     = 2 + 3 + sum [4,5]
     = 2 + 3 + 4 + sum [5]
     = 2 + 3 + 4 + 5 + sum []
     = 2 + 3 + 4 + 5 + 0
     = 14

length [1,2,3,4] + sum [1,2,3,4]
     = 1 + length [2,3,4] + 1 + sum [2,3,4]
     = 1 + 1 + length [3,4] + 1 + 2 + sum [3,4]
     = 1 + 1 + 1 + length [4] + 1 + 2 + 3 + sum [4]
     = 1 + 1 + 1 + 1 + length [] + 1 + 2 + 3 + 4 + sum []
     = 1 + 1 + 1 + 1 + 0 + 1 + 2 + 3 + 4 + 0
     = 4 + 10
     = 14

Exercise 9.
Generalized Theorem 20: sum (map (k+) xs = k * length xs + sum xs

xs = [1,2,3,4], k = 3
sum (map (3+) [1,2,3,4] )
     = sum (3+1 : map (3+) [2,3,4] )
     = sum ( 3+1 : 3+2 : map (3+) [3,4] )
     = sum ( 3+1 : 3+2 : 3+3 : map (3+) [4] )
     = sum ( 3+1 : 3+2 : 3+3 : 3+4 : map (3+) [] )
     = sum ( 3+1 : 3+2 : 3+3 : 3+4 : [] )
     = sum ( 4 : 5 : 6 : 7 : [] )
     = sum ( 4 : 5 : 6 : [7] )
     = sum ( 4 : 5 : [6,7] )
     = sum ( 4 : [5,6,7] )
     = sum [4,5,6,7]
     = 4 + sum [5,6,7]
     = 4 + 5 + sum [6,7]
     = 4 + 5 + 6 + sum [7]
     = 4 + 5 + 6 + 7 + sum []
     = 4 + 5 + 6 + 7 + 0
     = 22

3 * length [1,2,3,4] + sum [1,2,3,4]
     = 3 * (1 + length [2,3,4]) + 1 + sum [2,3,4]
     = 3 * (1 + 1 + length [3,4]) + 1 + 2 + sum [3,4]
     = 3 * (1 + 1 + 1 + length [4]) + 1 + 2 + 3 + sum [4]
     = 3 * (1 + 1 + 1 + 1 + length []) + 1 + 2 + 3 + 4 + sum []
     = 3 * (1 + 1 + 1 + 1 + 0) + 1 + 2 + 3 + 4 + 0
     = 3*4 + 10
     = 22

Theorem: sum (map (k+) xs = k*length xs + sum xs

Proof. Induction over xs. The base case is

sum (map (k+) [])
     = sum []                { map.1 }
     = 0 + sum []            { 0 + x = x }
     = length [] + sum []    { length.1 }

Inductive case. Assume sum (map (k+) xs) = k*length xs + sum xs
sum (map (+k) (x:xs))
     = sum ((k+x) : map (k+) xs)             { map.2 }
     = (k + x) + sum (map (k+) xs)           { sum.2 }
     = (k + x) + (k*length xs + sum xs)      { hypothesis }
     = (k + k*length xs) + (x + sum xs)      { (+).algebra }
     = k*(1 + length xs) + (x + sum xs)      { (*).algebra }
     = k*length (x:xs) + sum (x:xs)          { length.2, sum.2}
QED

4.6 Functional Equality

Theorem 25. map f . concat = concat (map (map f)).

Exercise 10. Prove Theorem 25.
Proof. The theorem states that two functions are equal. Therefore, we use the
definition of extensional equality of functions; thus we choose an arbitrary 
list of lists xss, and we must prove that 

map f (concat xss) = concat (map (map f) xss). 

This has been proved by Theorem 22.

QED

Exercise 11. Prove that the ++ operator is associative.

Theorem 109. (xs++ys)++zs = xs++(ys++zs)

Proof. By induction over xs. Base case. Let xs = [].

([]++ys)++zs
     = ys++zs                { (++).1 }
     = []++(ys++zs)          { (++).1 }

Inductive case. Assume the hypothesis, (xs++ys)++zs = xs++(ys++zs).

((x:xs)++ys)++zs
     = (x : (xs++ys))++zs    { (++).2 }
     = x : (xs++ys)++zs      { (++).2 }
     = x : xs++(ys++zs)      { hypothesis }
     = (x:xs)++(ys++zs)

QED

Exercise 12. Prove sum . map length = length . concat

Proof. The theorem states that two functions are equal. Therefore, we use 
the definition of extensional equality of functions; thus we choose an 
arbitrary list of lists xss, and we must prove that

sum . map length xss = length . concat xss

Proof. By induction. Base case.

sum . map length []
     = sum (map length [])                   { (.) }
     = sum []                                { map.1 }
     = 0                                     { sum.1 }
     = length []                             { length.1 }
     = length (concat [])                    { concat.1 }
     = length . concat []                    { (.) }

Inductive case. Assume the hypothesis 
sum . map length xss = length . concat xss. We must prove
sum . map length xs:xss = length . concat xs:xss.

sum . map length xs:xss
     = sum (map length xs:xss)               { (.) }
     = sum (length xs : map length xss)      { map.2 }
     = length xs + sum (map length xss)      { sum.2 }
     = length xs + sum . map length xss      { (.) }
     = length xs + length . concat xss       { hypothesis }
     = length xs + length (concat xss)       { (.) }
     = length (xs ++ concat xss)             { Theorem 16 }
     = length (concat (xs:xss))              { concat.2 }
     = length . concat (xs:xss)              { (.) }

QED

4.8 Limitations of Induction

Exercise 14. xss must be composed of finite lists. If xs in (xs:xss) is not
finite, concat.2 will occur indefinitely.

Exercise 15.

Theorem 27. reverse . reverse = id

>reverse :: [a] -> [a]
>reverse []     = []
>reverse (x:xs) = reverse xs ++ [x]

reverse . reverse [1,2,3]
     = reverse (reverse [1,2,3])
     = reverse (reverse [2,3] ++ [1])
     = reverse (reverse [3] ++ [2] ++ [1])
     = reverse (reverse [] ++ [3] ++ [2] ++ [1])
     = reverse ([] ++ [3] ++ [2] ++ [1])
     = reverse [3,2,1]
     = reverse [2,1] ++ [3]
     = reverse [1] ++ [2] ++ [3]
     = reverse [] ++ [1] ++ [2] ++ [3]
     = [] ++ [1] ++ [2] ++ [3]
     = [1,2,3]
     = id [1,2,3]

Exercise 16. Prove reverse (xs++ys) = reverse ys ++ reverse xs
Then decide whether this list theorem happens to be true for infinite
lists like [1..].

Proof. By induction over xs. The base case:

reverse ([]++ys)
     = reverse ys                                    { (++).1 }
     = reverse ys ++ []                              { (++).2 }
     = reverse ys ++ reverse []                      { reverse.1 }

The inductive case. The hypothesis is 
reverse (xs++ys) = reverse ys ++ reverse xs

reverse ((x:xs)++ys)
     = reverse (x : (xs++ys))                        { (++).2 }
     = reverse (xs++ys) ++ [x]                       { reverse.2 }
     = reverse ys ++ reverse xs ++ [x]               { hypothesis }
     = reverse ys ++ reverse (x:xs)                  { reverse.2 }
QED

This list theorem does not work for infinite lists like [1..]. It will be
impossible for reverse (xs++ys) : x to complete operation since 
reverse (xs++ys) is an infinitely long list and cannot be prepended to
another list.

Exercise 17. Prove Theorem 27. reverse . reverse xs = xs.

Proof. By induction. The base case.

reverse . reverse []
     = reverse (reverse [])                          { (.) }
     = reverse []                                    { reverse.1 }
     = []                                            { reverse.1 }

The inductive case. The hypothesis is reverse . reverse xs = xs.

reverse . reverse (x:xs)
     = reverse (reverse (x:xs))                      { (.) }
     = reverse (reverse xs ++ [x])                   { reverse.2 }
     = reverse [x] ++ reverse (reverse xs)           { Theorem Ex. 16}
     = reverse [x] ++ xs                             { hypothesis }
     = [x] ++ xs                                     { reverse.2 }
     = (x:xs)                                        { (++).2 }

QED

Exercise 18. Theorem 27 does not hold for infinite lists because reversing
an infinite list is an infinitely long operation.

4.10 Review Exercises

Exercise 19. length (concat xss) = sum (map length xss)

Also proven in Exercise 12.

Proof by induction. The base case.

length (concat [])
     = length []                                     { concat.1 }
     = 0                                             { length.1 }
     = sum []                                        { sum.1 }
     = map length []                                 { map.1 }

The inductive case. The hypothesis is length (concat xss) = sum (map length xss).

length (concat (xs:xss)) =
     = length (xs ++ concat xss)                     { concat.2}
     = length xs + length (concat xss)               { Theorem 16 }
     = length xs + sum (map length xss)              { hypothesis }
     = sum (length xs : map length xss)              { sum.2 }
     = sum (map length (xs:xss))                     { map.2 }

QED

>and, or          :: [Bool] -> Bool
>and              =  foldr (&&) True
>or               =  foldr (||) False

Exercise 20. Prove that or xs returns True if True is one element in xs.

Proof. Assume xs is of type [Bool], it has n+1 elements, and True is one 
element in xs.

P(n) = or xs = True

By induction. The base case. (n = 0)

or xs
        = or [True]                             { xs = [True] }
        = foldr (||) False ([True])             { or }
        = (||) True (foldr (||) False [])       { foldr.2 }
        = (||) True (False)                     { foldr.2}
        = True                                  { (||) }

The inductive case.

or xs
        = foldr (||) False xs                   { or }
        = foldr (||) False (y:ys)               { xs = (y:ys)}
        = (||) y (foldr (||) False ys)          { foldr.2 }
        = (||) y (or ys)                        { or }

There are two cases. Case 1: y = True

        = (||) True (or ys)                     { y = True }
        = True                                  { (||) }

Case 2: or ys = True

        = (||) y True                           { hypothesis }
        = True                                  { (||) }

QED

Exercise 21. Prove that and xs returns True if all elements in xs are True.

P(n) = and xs = True

By induction. The base case. (n = 0)

or xs
        = and [True]                            { xs = [True] }
        = foldr (&&) True ([True])              { and }
        = (&&) True (foldr (&&) True [])        { foldr.2 }
        = (&&) True (True)                      { foldr.2}
        = True                                  { (&&) }

The inductive case. The hypothesis is and xs = True

or xs
        = foldr (&&) True xs                    { and }
        = foldr (&&) True (y:ys)                { xs = (y:ys)}
        = (&&) y (foldr (&&) True ys)           { foldr.2 }
        = (&&) True (foldr (&&) True ys)        { y = True }
        = (&&) True (and ys)                    { and }
        = (&&) True (True)                      { hypothesis }
        = True                                  { (&&) }

QED

Exercise 22.

max x y = x     if x >= y
max x y = y     if y >= x

>maximum :: Ord a => [a] -> a
>maximum (x:xs) = foldr max x xs

Exercise 23. Prove that maximum has the following property:

(maximum xs) >= x

where x is an arbitrary element of xs.

Let xs = (x:xs')

Proof. By induction. Base case: Assume length xs' = 0 so that xs = (x:[]).

maximum xs
        = foldr max x []        { maximum }
        = x                     { foldr.1 }

In this case, (maximum xs) = x.

Inductive case. Assume the hypothesis (maximum xs) >= x.

maximum (x:x':xs')
        = foldr max x (x':xs') { maximum }
        = max x' (foldr max x xs') { foldr.2 }
        = max x' (maximum (x:xs')) { maximum }
        = max x' (maximum xs)   { xs = (x:xs') }

Case 1: (maximum xs) < x'

In this case, max x' (maximum xs) = x'. Therefore maximum (x':xs) = x'.

Case 2: (maximum xs) > x'

Here, max x' (maximum xs) = maximum xs. Therefore, maximum (x':xs) > x'.

Therefore, maximum (x:x':xs') >= x'.

QED
