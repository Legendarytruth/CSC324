{-|
Module: CPSBork Assignment 2
Description: Continuation Passing Style Transformations
Copyright: (c) University of Toronto, 2019
               CSC324 Principles of Programming Languages, Fall 2019

* Before starting, please review the exercise guidelines at
http://www.cs.toronto.edu/~lczhang/324/homework.html *

-}
-- This lists what this module exports. Don't change this!

module CPSBork (
    -- Warmup
    cpsFacEnv, fibEnv, cpsFibEnv,
    -- CPS Transform
    cpsDef, cpsExpr
) where

import qualified Data.Map as Map
import Test.QuickCheck (quickCheck)
import Ex10Bork (Env, emptyEnv, Value(..), HaskellProc(..), Expr(..), eval, def)

------------------------------------------------------------------------------
-- Warmup
------------------------------------------------------------------------------

-- | facEnv is an environment containing the function `fac` that computes the 
--   factorial of a number, written in direct style.
facEnv :: Env
facEnv = def [("fac", Lambda ["n"]
                (If (Equal (Var "n") (Literal $ Num 0))
                    (Literal $ Num 1)
                    (Times (Var "n") (App (Var "fac")
                       [(Plus (Var "n") (Literal $ Num (-1)))]))))]

-- | cpsFacEnv is an environment containing the function `cps_fac` that computes the 
--   factorial of a number, written in CPS
cpsFacEnv :: Env
cpsFacEnv = def [("cps_fac", Lambda ["n", "k"]
                (If (Equal (Var "n") (Literal $ Num 0))
                    (App (Var "k") [(Literal (Num 1))])
                    (App (Var "cps_fac") [(Plus (Var "n") (Literal (Num (-1)))), (Lambda ["res"] (App (Var "k") [(Times (Var "n") (Var "res"))]))])))]

-- | fibEnv is an environment containing the function `fib` that computes the 
--   n-th fibonacci via recursion, written in direct style.
fibEnv :: Env
fibEnv = def [("fib", Lambda ["n"]
                (If (Equal (Var "n") (Literal (Num 0)))
                    (Literal (Num 0))
                    (If (Equal (Var "n") (Literal (Num 1)))
                        (Literal (Num 1))
                        (Plus (App (Var "fib") [(Plus (Var "n") (Literal (Num (-1))))]) (App (Var "fib") [(Plus (Var "n") (Literal (Num (-2))))])))))]

-- | cpsFfibEnv is an environment containing the function `fib` that computes the 
--   n-th fibonacci via recursion, written in direct style.
cpsFibEnv :: Env
cpsFibEnv = def [("cps_fib", Lambda ["n", "k"]
                    (If (Equal (Var "n") (Literal $ Num 0))
                    (App (Var "k") [(Literal (Num 0))])
                    (If (Equal (Var "n") (Literal $ Num 1))
                    (App (Var "k") [(Literal (Num 1))])
                    (App (Var "cps_fib") [(Plus (Var "n") (Literal (Num (-1)))), (Lambda ["res1"] 
                    (App (Var "cps_fib") [(Plus (Var "n") (Literal (Num (-2)))), (Lambda ["res2"] 
                    (App (Var "k") [(Plus (Var "res1") (Var "res2"))]))]))]))))]

-- | An identity function in Bork, used for testing
identityFn :: Expr
identityFn = Lambda ["x"] (Var "x")

-- | Some simple tests. You should write your own.

prop_testFac :: Bool
prop_testFac = eval facEnv (App (Var "fac") [Literal $ Num 3]) == Num 6
prop_testCpsFac :: Bool
prop_testCpsFac = eval cpsFacEnv (App (Var "cps_fac") [Literal $ Num 3, identityFn]) == Num 6

------------------------------------------------------------------------------
-- CPS Transformation
------------------------------------------------------------------------------

-- | Performs CPS Transformations on a list of name -> expression bindings
-- by renaming the names, and CPS transforming the expressions
cpsDef :: [(String, Expr)] -> [(String, Expr)]
cpsDef bindings = map (\(s, e) -> (rename s, cpsExpr e "" id)) bindings 

-- | CPS Transform a single expression
cpsExpr :: Expr -> String -> (Expr -> Expr) -> Expr
-- literals:
cpsExpr (Literal v) s context = context (Literal v)
-- variables:
cpsExpr (Var name)  s context =  context (Var (rename name))
-- builtins:
cpsExpr (Plus left right)  s context = cpsExpr left s (\leftV -> cpsExpr right s (\rightV -> context (Plus leftV rightV)))
cpsExpr (Times left right) s context = cpsExpr left s (\leftV -> cpsExpr right s (\rightV -> context (Times leftV rightV)))
cpsExpr (Equal left right) s context = cpsExpr left s (\leftV -> cpsExpr right s (\rightV -> context (Equal leftV rightV)))
-- function definition:
cpsExpr (Lambda params body) s context = Lambda ((map rename params) ++ [newName (rename s) "k"]) (cpsExpr body s (\bodyV -> App (Var (newName (rename s) "k")) [bodyV]))
-- function application:
cpsExpr (App fn []) s context = App (cpsExpr fn s (\name -> name)) [Lambda [newName (rename s) "result"] (context (Var (newName (rename s) "result")))]
cpsExpr (App fn [x]) s context = cpsExpr x (rename s) (\res -> App (cpsExpr fn s (\name -> name)) [res, Lambda [newName (rename s) "result"] (context (Var (newName (rename s) "result")))])
cpsExpr (App fn [x, y]) s context = cpsExpr x (rename s) (\res1 -> cpsExpr y (rename s) (\res2 -> App (cpsExpr fn s (\name -> name)) [res1, res2, Lambda [newName (rename s) "result"] (context (Var (newName (rename s) "result")))]))
cpsExpr (App fn [x, y, z]) s context = cpsExpr x (rename s) (\res1 -> cpsExpr y (rename s) (\res2 -> cpsExpr z (rename s) (\res3 -> App (cpsExpr fn s (\name -> name)) [res1, res2, res3, Lambda [newName (rename s) "result"] (context (Var (newName (rename s) "result")))])))
cpsExpr (App fn [x, y, z, a]) s context = cpsExpr x (rename s) (\res1 -> cpsExpr y (rename s) (\res2 -> cpsExpr z (rename s) (\res3 -> cpsExpr a (rename s) (\res4 -> App (cpsExpr fn s (\name -> name)) [res1, res2, res3, res4, Lambda [newName (rename s) "result"] (context (Var (newName (rename s) "result")))]))))
cpsExpr (App fn [x, y, z, a, b]) s context = cpsExpr x (rename s) (\res1 -> cpsExpr y (rename s) (\res2 -> cpsExpr z (rename s) (\res3 -> cpsExpr a (rename s) (\res4 -> cpsExpr b (rename s) (\res5 -> App (cpsExpr fn s (\name -> name)) [res1, res2, res3, res4, res5, Lambda [newName (rename s) "result"] (context (Var (newName (rename s) "result")))])))))
-- if expressions
cpsExpr (If cond conseq altern) s context = cpsExpr cond (rename s) (\result1 -> context (If result1 (cpsExpr conseq (rename (rename s)) (\same -> same)) (cpsExpr altern (rename (rename (rename s))) (\same -> same))))
--cpsExpr (If cond conseq altern) s context = cpsExpr cond s (\result1 -> cpsExpr conseq s (\result2 -> cpsExpr altern s (\result3 -> 
 --   context (If result1 result2 result3))))

--cpsMap :: (Expr -> String -> (Expr -> Expr) -> Expr) -> [Expr] -> String -> (Expr -> Expr) -> [Expr]
--cpsMap cpsExpr lists s context = 

-- | Helper function that renames a variable by prepending "cps_"
rename :: String -> String
rename s = "cps_" ++ s

newName :: String -> String -> String
newName s result = s ++ result
-- | Some simple tests. You should also write your own.

prop_testCpsExprLiteral :: Bool
prop_testCpsExprLiteral = result == Num 1
    where bindings = cpsDef [("n", Literal $ Num 1)]
          env = def bindings
          result = eval env $ Var ("cps_n")

prop_testCpsExprVar :: Bool
prop_testCpsExprVar = result == Num 2
    where bindings = cpsDef [("n", Literal $ Num 2),
                             ("m", Var "n")]
          env = def bindings
          result = eval env $ Var ("cps_m")

prop_testCpsExprPlus :: Bool
prop_testCpsExprPlus = result == Num 5
    where bindings = cpsDef [("n", Literal $ Num 2),
                             ("m", (Plus (Var "n") (Literal $ Num 3)))]
          env = def bindings
          result = eval env $ Var "cps_m"

prop_testCpsExprFac :: Bool
prop_testCpsExprFac = result == Num 120
    where bindings = cpsDef [("fac", Lambda ["n"]
                                (If (Equal (Var "n") (Literal $ Num 0))
                                    (Literal $ Num 1)
                                    (Times (Var "n") (App (Var "fac")
                                       [(Plus (Var "n") (Literal $ Num (-1)))]))))]
          env = def bindings
          result = eval env $ (App (Var "cps_fac") [Literal $ Num 5, identityFn])

prop_testCpsExprFib :: Bool
prop_testCpsExprFib = result == Num 3
    where bindings = cpsDef [("fib", Lambda ["n"]
                                (If (Equal (Var "n") (Literal (Num 0)))
                                    (Literal (Num 0))
                                    (If (Equal (Var "n") (Literal (Num 1)))
                                        (Literal (Num 1))
                                        (Plus (App (Var "fib") [(Plus (Var "n") (Literal (Num (-1))))]) (App (Var "fib") [(Plus (Var "n") (Literal (Num (-2))))])))))]

          env = def bindings
          result = eval env $ (App (Var "cps_fib") [Literal $ Num 4, identityFn])
------------------------------------------------------------------------------
-- Main
------------------------------------------------------------------------------

-- | This main function runs the quickcheck tests.
-- This gets executed when you compile and run this program. We'll talk about
-- "do" notation much later in the course, but for now if you want to add your
-- own tests, just define them above, and add a new `quickcheck` line here.
main :: IO ()
main = do
    quickCheck prop_testFac
    quickCheck prop_testCpsFac
    quickCheck prop_testCpsExprLiteral 
    quickCheck prop_testCpsExprVar 
    quickCheck prop_testCpsExprPlus
    quickCheck prop_testCpsExprFac 
    quickCheck prop_testCpsExprFib
