Chapter 5 Trees

5.2 Representing Trees in Haskell

>data BinTreeInt
>       = Leaf
>       | Node Integer BinTreeInt BinTreeInt

>tree1 :: BinTreeInt
>tree1 = Leaf

>tree2 :: BinTreeInt
>tree2 = Node 23 Leaf Leaf

>tree3 :: BinTreeInt
>tree3 =
>   Node 4
>       (Node 2
>           (Node 1 Leaf Leaf)
>           (Node 3 Leaf Leaf))
>       (Node 7
>           (Node 5
>               Leaf
>               (Node 6 Leaf Leaf))
>           (Node 8 Leaf Leaf))

>data BinTree a
>   = BinLeaf
>   | BinNode a (BinTree a) (BinTree a)
>   deriving Show

>tree4 :: BinTree String
>tree4 = BinNode "cat" BinLeaf (BinNode "dog" BinLeaf BinLeaf)

>tree5 :: BinTree (Integer,Bool)
>tree5 = BinNode (23,False)
>           BinLeaf
>           (BinNode (49,True) BinLeaf BinLeaf)

>tree6 :: BinTree Int
>tree6 = BinNode 4
>           (BinNode 2
>               (BinNode 1 BinLeaf BinLeaf)
>               (BinNode 3 BinLeaf BinLeaf))
>           (BinNode 6
>               (BinNode 5 BinLeaf BinLeaf)
>               (BinNode 7 BinLeaf BinLeaf))

>-- treeBad = BinNode 'c'
>--            (BinNode True BinLeaf BinLeaf)
>--            (BinNode False BinLeaf BinLeaf)

Hugs>:load chapter05.lhs
ERROR "chapter05.lhs":47 - Type error in application
*** Expression     : BinNode 'c' (BinNode True BinLeaf BinLeaf) (BinNode False BinLeaf BinLeaf)
*** Term           : 'c'
*** Type           : Char
*** Does not match : Bool

Exercise 1.

>data Tree1
>   = Tree1Leaf
>   | Tree1Node Char Integer
>       Tree1 Tree1 Tree1

Exercise 2.

>data Tree2
>   = Tree2Leaf
>   | Tree2Node Integer [Tree2]

5.3 Processing Trees with Recursion

5.3.1 Tree Traversal

>inorder :: BinTree a -> [a]
>inorder BinLeaf = []
>inorder (BinNode x t1 t2) = inorder t1 ++ [x] ++ inorder t2

>preorder :: BinTree a -> [a]
>preorder BinLeaf = []
>preorder (BinNode x t1 t2) = [x] ++ preorder t1 ++ preorder t2

>postorder :: BinTree a -> [a]
>postorder BinLeaf = []
>postorder (BinNode x t1 t2) =
>   postorder t1 ++ postorder t2 ++ [x]

The inorder traversal of a small tree:

inorder (BinNode 4 (BinNode 8 BinLeaf BinLeaf) BinLeaf)
= inorder (BinNode 8 BinLeaf BinLeaf) ++ [4] ++ inorder BinLeaf
= (inorder BinLeaf ++ [8] ++ inorder BinLeaf) ++ [4] ++ []
= ([] ++ [8] ++ []) ++ [4] ++ []
= [8, 4]

Exercise 3.

inorder tree3
    = inorder (Node 4
        (Node 2 (Node 1 Leaf Leaf) (Node 3 Leaf Leaf))
        (Node 7 (Node 5 Leaf (Node 6 Leaf Leaf)) (Node 8 Leaf Leaf)))
    =   inorder (Node 2 (Node 1 Leaf Leaf) (Node 3 Leaf Leaf))
    ++ [4] ++
        inorder (Node 7 (Node 5 Leaf (Node 6 Leaf Leaf)) (Node 8 Leaf Leaf))
    =   (
            inorder (Node 1 Leaf Leaf)
        ++ [2] ++
            inorder (Node 3 Leaf Leaf)
        )
    ++ [4] ++
        (
            inorder (Node 5 Leaf (Node 6 Leaf Leaf))
        ++ [7] ++
            inorder (Node 8 Leaf Leaf)
        )
    =   (
                inorder Leaf
            ++ [1] ++
                inorder Leaf
        ++ [2] ++
                inorder Leaf
            ++ [3] ++
                inorder Leaf
        )
    ++ [4] ++
        (
                inorder Leaf
            ++ [5] ++
                inorder (Node 6 Leaf Leaf)
        ++ [7] ++
                inorder Leaf
            ++ [8] ++
                inorder Leaf
        )
    =   (
                []
            ++ [1] ++
                []
        ++ [2] ++
                []
            ++ [3] ++
                []
        )
    ++ [4] ++
        (
                []
            ++ [5] ++
                    inorder Leaf
                ++ [6] ++
                    inorder Leaf
        ++ [7] ++
                []
            ++ [8] ++
                []
        )
    =   (
                []
            ++ [1] ++
                []
        ++ [2] ++
                []
            ++ [3] ++
                []
        )
    ++ [4] ++
        (
                []
            ++ [5] ++
                    []
                ++ [6] ++
                    []
        ++ [7] ++
                []
            ++ [8] ++
                []
        )
    = [1,2,3,4,5,6,7,8]

Exercise 4.

f :: a -> b

>inorderf :: (a->b) -> BinTree a -> [b]
>inorderf f BinLeaf = []
>inorderf f (BinNode x t1 t2) = inorderf f t1 ++ [f x] ++ inorderf f t2

inorder tree6 ==> [1,2,3,4,5,6,7]
inorderf (2*) tree6 ==> [2,4,6,8,10,12,14]

5.3.2 Processing Tree Structures

>reflect :: BinTree a -> BinTree a
>reflect BinLeaf = BinLeaf
>reflect (BinNode n l r) = BinNode n (reflect r) (reflect l)

>height :: BinTree a -> Integer
>height BinLeaf = 0
>height (BinNode x t1 t2) = 1 + max (height t1) (height t2)

size :: BinTreeInt -> Int
size Leaf = 0
size (Node x t1 t2) = 1 + size t1 + size t2

>size :: BinTree a -> Integer
>size BinLeaf = 0
>size (BinNode x t1 t2) = 1 + size t1 + size t2

>balanced :: BinTree a -> Bool
>balanced BinLeaf = True
>balanced (BinNode x t1 t2) =
>   balanced t1 && balanced t2 && (height t1 == height t2)

Exercise 5.

>tallTree7 :: BinTree Int
>tallTree7 =
>   BinNode 7 (
>       BinNode 6 (
>           BinNode 5 (
>               BinNode 4 (
>                   BinNode 3 (
>                       BinNode 2 (
>                           BinNode 1
>                               BinLeaf
>                               BinLeaf)
>                           BinLeaf)
>                       BinLeaf)
>                   BinLeaf)
>               BinLeaf)
>           BinLeaf)
>       BinLeaf

size tallTree7 ==> 7
height tallTree7 ==> 7

>shortTree7 :: BinTree Int
>shortTree7 =
>   BinNode 4
>       (BinNode 2 (BinNode 1 BinLeaf BinLeaf) (BinNode 3 BinLeaf BinLeaf))
>       (BinNode 6 (BinNode 5 BinLeaf BinLeaf) (BinNode 7 BinLeaf BinLeaf))

size shortTree7 ==> 7
height shortTree7 ==> 3

Exercise 6.

balanced :: BinTree a -> Bool
balanced BinLeaf = True
balanced (BinNode x t1 t2) = balanced t1 && balanced t2

The above definition of balanced returns True for tallTree7, defined in
Exercise 5. tallTree7 is unbalanced.

Exercise 7.

balanced :: BinTree a -> Bool
balanced BinLeaf = True
balanced (BinNode x t1 t2) = height t1 == height t2

unbalancedTree :: BinTree Int
unbalancedTree = BinNode 1
    (BinNode 2 (BinNode 3 BinLeaf BinLeaf) BinLeaf)
    (BinNode 4 (BinNode 5 BinLeaf BinLeaf) BinLeaf)

unbalancedTree, defined above, returns True for the modified definition of
balanced.

5.3.3 Evaluating Expression Trees

>data Exp
>   = Const Integer
>   | Add Exp Exp
>   | Mult Exp Exp

>eval :: Exp -> Integer
>eval (Const n) = n
>eval (Add e1 e2) = eval e1 + eval e2
>eval (Mult e1 e2) = eval e1 * eval e2

5.3.4 Binary Search Trees

>linSearch :: Eq a => a -> [(a,b)] -> Maybe b
>linSearch k [] = Nothing
>linSearch k ((x,y):xs) =
>   if k==x
>       then Just y
>       else linSearch k xs

>bstSearch :: Ord a => a -> BinTree (a,b) -> Maybe b
>bstSearch key BinLeaf = Nothing
>bstSearch key (BinNode (x,y) t1 t2) =
>   if key == x
>       then Just y
>       else if key < x
>           then bstSearch key t1
>           else bstSearch key t2

>insert :: Ord a => (a,b) -> BinTree (a,b) -> BinTree (a,b)
>insert (key,d) BinLeaf = BinNode (key,d) BinLeaf BinLeaf
>insert (key,d) (BinNode (x,y) t1 t2) =
>   if key == x
>       then BinNode (key,d) t1 t2
>       else if key < x
>           then BinNode (x,y) (insert (key,d) t1) t2
>           else BinNode (x,y) t1 (insert (key,d) t2)

Exercise 8.

>mapTree :: (a->b) -> BinTree a -> BinTree b
>mapTree f BinLeaf = BinLeaf
>mapTree f (BinNode x t1 t2) = BinNode (f x) (mapTree f t1) (mapTree f t2)

Exercise 9.

concatTree (Node [2] (Node [3,4] Tip Tip))
           (Node [5] Tip Tip)
==> [3,4,2,5]

>concatTree :: (BinTree [a]) -> [a]
>concatTree BinLeaf = []
>concatTree (BinNode xs t1 t2) = concatTree t1 ++ xs ++ concatTree t2

concatTree (BinNode [2] (BinNode [3,4] BinLeaf BinLeaf)
                        (BinNode [5] BinLeaf BinLeaf))
==> [3,4,2,5]

Exercise 10.

>zipTree :: (BinTree a) -> (BinTree b) -> Maybe [(a,b)]
>zipTree BinLeaf           BinLeaf           = Just []
>zipTree (BinNode x ll lr) BinLeaf           = Nothing
>zipTree BinLeaf           (BinNode y rl rr) = Nothing
>zipTree (BinNode x ll lr) (BinNode y rl rr) =
>   case zipTree ll rl of
>       Nothing -> Nothing
>       Just ls -> case zipTree lr rr of
>           Nothing -> Nothing
>           Just rs -> Just (ls ++ [(x,y)] ++ rs)

zipTree (BinNode 2 (BinNode 1 BinLeaf BinLeaf) (BinNode 3 BinLeaf BinLeaf))
        (BinNode 5 (BinNode 4 BinLeaf BinLeaf) (BinNode 6 BinLeaf BinLeaf))
==> Just [(1,4),(2,5),(3,6)]

zipTree (BinNode 2 (BinNode 1 BinLeaf BinLeaf) (BinNode 3 BinLeaf BinLeaf))
        (BinNode 5 (BinNode 4 BinLeaf BinLeaf) BinLeaf)
==> Nothing
