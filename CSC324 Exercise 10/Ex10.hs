{-|
Module: Ex10
Description: Exercise 10: Continuation Passing Style
Copyright: (c) University of Toronto, 2019
               CSC324 Principles of Programming Languages, Fall 2019

* Before starting, please review the exercise guidelines at
http://www.cs.toronto.edu/~lczhang/324/homework.html *

-}
-- This lists what this module exports. Don't change this!

module Ex10 (
    -- Task 1
    cpsFactorial, cpsFibonacci, cpsLength, cpsMap,
    cpsMergeSort, cpsSplit, cpsMerge,
    -- Task 2
    cpsEval
) where

import qualified Data.Map as Map
import Test.QuickCheck (quickCheck)
import Ex10Types (Env, emptyEnv, Value(..), HaskellProc(..), Expr(..))

------------------------------------------------------------------------------
-- * Task 1. CPS Transforming Haskell Functions *
------------------------------------------------------------------------------

-- | Compute the factorial of a number
-- factorial :: Int -> Int

-- | Compute the factorial of a number, in continuation passing style
cpsFactorial:: Int -> (Int -> r) -> r
cpsFactorial n k = if n == 0 then (k 1) else cpsFactorial(n - 1) $ \x -> k (x * n)

-- | Compute the n-th fibonacci number F(n).
--    Recall F(0) = 0, F(1) = 1, and F(n) = F(n-1) + F(n-2)
-- fibonacci :: Int -> Int

-- | Compute the n-th fibonacci number F(n), in continuation passing style
cpsFibonacci:: Int -> (Int -> r) -> r
cpsFibonacci n k = if n == 0 then (k 0) else if n == 1 then (k 1) else cpsFibonacci(n - 1) (\x -> cpsFibonacci (n-2) (\y -> k(x+y)))

-- | Sample tests:
prop_testFactorial :: Bool
prop_testFactorial = (cpsFactorial 3 id) == 6
prop_testFibonacci :: Bool
prop_testFibonacci = (cpsFibonacci 6 id) == 8

------------------------------------------------------------------------------
-- | List functions

-- | CPS transform of the function `length`, which computes the length of a list
cpsLength :: [a] -> (Int -> r) -> r
cpsLength [] k = (k 0)
cpsLength (x:xs) k = cpsLength xs $ \r -> k(r + 1)


-- | CPS transform of the function `map`. The argument function (to be applied
--   every element of the list) is written in direct style
cpsMap :: (a -> b) -> [a] -> ([b] -> r) -> r
cpsMap f [] k = (k [])
cpsMap f (x:xs) k = (cpsMap f xs) $ \r -> k([f x] ++ r)
-- cpsMap f x k  = (cpsMap f (tail x)) $ \r -> k([f (head x)] ++ r)

-- | Sample tests:
prop_cpsLength :: Bool
prop_cpsLength = (cpsLength [1,2,3] id) == 3
prop_cpsMap :: Bool
prop_cpsMap = (cpsMap (2*) [1,2,3,4,5] id) == [2,4,6,8,10]

------------------------------------------------------------------------------
-- Merge Sort

-- | Sort a list using mergeSort
-- mergeSort :: [Int] -> [Int]

-- | Split a list into two lists. All list elements in even indices
-- is placed in one sub-list, and all list elements in odd indicies
-- is placed in the second sub-list.
-- split :: [Int] -> ([Int], [Int])

-- | Merge two sorted lists together
-- merge :: [Int] -> [Int] -> [Int]

-- | CPS transform of mergeSort
cpsMergeSort :: [Int] -> ([Int] -> r) -> r
cpsMergeSort lst k = if lst == [] then (k lst) else undefined  
    
-- | CPS transform of split
cpsSplit :: [Int] -> (([Int], [Int]) -> r) -> r
cpsSplit [l1] k = k([l1], [])
cpsSplit lst k = if lst == [] then k ([],[]) else
    cpsSplit (tail lst) $ \x -> if ((cpsLength lst) mod 2 == 0) then k (([(head lst)] ++ (fst x)), (snd x))  else k ((fst x),([(head lst)] ++ (snd x)))

-- | CPS transform of merge
cpsMerge :: [Int] -> [Int] -> ([Int] -> r) -> r
cpsMerge [] [] k = (k [])
cpsMerge [l1] [l2] k = if l1 < l2 then k ([l1] ++ [l2]) else k ([l2] ++ [l1])
cpsMerge lst [] k = (k lst)
cpsMerge [] lst k = (k lst)

-- | Sample test:
prop_cpsMergeSort :: Bool
prop_cpsMergeSort = (cpsMergeSort [1,2,4,3] id) == [1,2,3,4]

------------------------------------------------------------------------------
-- * Task 2. CPS Transforming The Bork Interpreter *
------------------------------------------------------------------------------

-- | A CPS interpreter `eval` for Bork, which takes an environment,
--   an expression, and a continuation, and calls the continuation with
--   the evaluated value.
--   Notice that the type signature of `eval` is less general compared to
--   usual, i.e. it is not:
--      Env -> Expr -> (Value -> r) -> r
--   This restriction on the type of the continuation makes it easier
--   to errors.
cpsEval :: Env -> Expr -> (Value -> Value) -> Value
cpsEval env (Literal value) k = (k value)
cpsEval env (Plus expr1 expr2) k = cpsEval env expr1 ( \ex1 -> cpsEval env expr2 ( \ex2 -> k(case (ex1, ex2) of
    (Num ex1, Num ex2) -> (Num (ex1 + ex2))
    _                  -> Error "plus")))
cpsEval env (Times expr1 expr2) k = cpsEval env expr1 ( \ex1 -> cpsEval env expr2 ( \ex2 -> k(case (ex1, ex2) of
    (Num ex1, Num ex2) -> (Num (ex1 * ex2))
    _                  -> Error "times")))
cpsEval env (Equal expr1 expr2) k = cpsEval env expr1 ( \ex1 -> cpsEval env expr2 (\ex2 -> k (if ex1 == ex2 then (k T) else (k F))))

cpsEval env (Var expr1) k = case (Map.lookup expr1 env) of 
    Just a -> (k a)
    Nothing -> Error "lookup"
cpsEval env (If conds thens elses) k = cpsEval env conds (\c -> cpsEval env thens (\t -> cpsEval env elses (\e -> if (c == T) then (k t) else (k e))))
cpsEval env (Lambda params body) k = k $ Procedure $ Proc (\values k2 ->
    let newEnv = Map.union (Map.fromList (zip params values)) env
    in cpsEval newEnv body k2)
cpsEval env (App proc [lst1]) k = cpsEval env lst1 (\l1 -> cpsEval env proc (\p -> k(case p of 
    Procedure (Proc func) -> func [l1] k
    _                     -> Error "apps" ))) 
cpsEval env (App proc [lst1, lst2]) k = cpsEval env lst1 (\l1 -> cpsEval env lst2 (\l2 -> cpsEval env proc (\p -> k(case p of 
    Procedure (Proc func) -> func [l1, l2] k
    _                     -> Error "apps" ))))
cpsEval env (App proc [lst1, lst2, lst3]) k = cpsEval env lst1 (\l1 -> cpsEval env lst2 
        (\l2 -> cpsEval env lst3 (\l3 -> cpsEval env proc (\p -> k(case p of 
    Procedure (Proc func) -> func [l1, l2, l3] k
    _                     -> Error "apps" )))))
cpsEval env (App proc [lst1, lst2, lst3, lst4]) k = cpsEval env lst1 (\l1 -> cpsEval env lst2 
        (\l2 -> cpsEval env lst3 (\l3 -> cpsEval env lst4 (\l4 -> cpsEval env proc (\p -> k(case p of 
    Procedure (Proc func) -> func [l1, l2, l3, l4] k
    _                     -> Error "apps" ))))))
cpsEval env (App proc [lst1, lst2, lst3, lst4, lst5]) k = cpsEval env lst1 (\l1 -> cpsEval env lst2 
        (\l2 -> cpsEval env lst3 (\l3 -> cpsEval env lst4 (\l4 -> cpsEval env lst5 (\l5 -> cpsEval env proc (\p -> k(case p of 
    Procedure (Proc func) -> func [l1, l2, l3, l4, l5] k
    _                     -> Error "apps" )))))))
cpsEval env (Shift str expr) k = undefined
cpsEval env (Reset expr) k = undefined


-- | Example: apply the identity function to the number 3
example1 = cpsEval emptyEnv (App (Lambda ["a"] (Var "a")) [Literal $ Num 3]) id

-- | Example: apply a function that returns 10 plus the second argument
--            to the arguments [1, 2]
example2 = cpsEval emptyEnv (App (Lambda ["a", "b"] (Plus (Literal $ Num 10) (Var "b")))
                              [Literal $ Num 1, Literal $ Num 2]) id
-- | Example: if statement expression
example3 = cpsEval emptyEnv (If (Equal (Literal F) (Literal F))
                             (Literal T)
                             (Literal F)) id

prop_cpsEvalExample1 :: Bool
prop_cpsEvalExample1 = example1 == Num 3
prop_cpsEvalExample2 :: Bool
prop_cpsEvalExample2 = example2 == Num 12
prop_cpsEvalExample3 :: Bool
prop_cpsEvalExample3 = example3 == T


------------------------------------------------------------------------------
-- Main
------------------------------------------------------------------------------

-- | This main function runs the quickcheck tests.
-- This gets executed when you compile and run this program. We'll talk about
-- "do" notation much later in the course, but for now if you want to add your
-- own tests, just define them above, and add a new `quickcheck` line here.
main :: IO ()
main = do
    quickCheck prop_testFactorial
    quickCheck prop_testFibonacci 
    quickCheck prop_cpsLength
    quickCheck prop_cpsMap
    --quickCheck prop_cpsMergeSort
    quickCheck prop_cpsEvalExample1
    quickCheck prop_cpsEvalExample2
    quickCheck prop_cpsEvalExample3
