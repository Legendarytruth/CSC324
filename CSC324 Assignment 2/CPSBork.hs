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
prop_testFib :: Bool
prop_testFib = eval fibEnv (App (Var "fib") [Literal $ Num 6]) == Num 8
prop_testCpsFib :: Bool
prop_testCpsFib = eval cpsFibEnv (App (Var "cps_fib") [Literal $ Num 6, identityFn]) == Num 8

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
cpsExpr (Plus left right)  s context = cpsExpr left (newName s "left") (\leftV -> cpsExpr right (newName s "right") (\rightV -> context (Plus leftV rightV)))
cpsExpr (Times left right) s context = cpsExpr left (newName s "left") (\leftV -> cpsExpr right (newName s "right") (\rightV -> context (Times leftV rightV)))
cpsExpr (Equal left right) s context = cpsExpr left (newName s "left") (\leftV -> cpsExpr right (newName s "right") (\rightV -> context (Equal leftV rightV)))
-- function definition:
cpsExpr (Lambda params body) s context = context (Lambda ((map rename params) ++ ["k"]) 
    (cpsExpr body s (\bodyV -> (App (Var "k") [bodyV]))))
-- function application:
cpsExpr (App fn []) s context = App (cpsExpr fn s (\name -> name)) [Lambda [newName (rename s) "result"] (context (Var (newName (rename s) "result")))]
cpsExpr (App fn [x]) s context = cpsExpr x (rename s) (\res -> App (cpsExpr fn s (\name -> name)) [res, Lambda [newName (rename s) "result"] (context (Var (newName (rename s) "result")))])
cpsExpr (App fn [x, y]) s context = cpsExpr x (rename s) (\res1 -> cpsExpr y (rename s) (\res2 -> App (cpsExpr fn s (\name -> name)) [res1, res2, Lambda [newName (rename s) "result"] (context (Var (newName (rename s) "result")))]))
cpsExpr (App fn [x, y, z]) s context = cpsExpr x (rename s) (\res1 -> cpsExpr y (rename s) (\res2 -> cpsExpr z (rename s) (\res3 -> App (cpsExpr fn s (\name -> name)) [res1, res2, res3, Lambda [newName (rename s) "result"] (context (Var (newName (rename s) "result")))])))
cpsExpr (App fn [x, y, z, a]) s context = cpsExpr x (rename s) (\res1 -> cpsExpr y (rename s) (\res2 -> cpsExpr z (rename s) (\res3 -> cpsExpr a (rename s) (\res4 -> App (cpsExpr fn s (\name -> name)) [res1, res2, res3, res4, Lambda [newName (rename s) "result"] (context (Var (newName (rename s) "result")))]))))
cpsExpr (App fn [x, y, z, a, b]) s context = cpsExpr x (rename s) (\res1 -> cpsExpr y (rename s) (\res2 -> cpsExpr z (rename s) (\res3 -> cpsExpr a (rename s) (\res4 -> cpsExpr b (rename s) (\res5 -> App (cpsExpr fn s (\name -> name)) [res1, res2, res3, res4, res5, Lambda [newName (rename s) "result"] (context (Var (newName (rename s) "result")))])))))
cpsExpr (App fn [x, y, z, a, b, c]) s context = cpsExpr x (rename s) (\res1 -> cpsExpr y (rename s) (\res2 -> cpsExpr z (rename s) (\res3 -> cpsExpr a (rename s) (\res4 -> cpsExpr b (rename s) (\res5 -> cpsExpr c (rename s) (\res6 -> App (cpsExpr fn s (\name -> name)) [res1, res2, res3, res4, res5, res6, Lambda [newName (rename s) "result"] (context (Var (newName (rename s) "result")))]))))))
cpsExpr (App fn [x, y, z, a, b, c, d]) s context = cpsExpr x (rename s) (\res1 -> cpsExpr y (rename s) (\res2 -> cpsExpr z (rename s) (\res3 -> cpsExpr a (rename s) (\res4 -> cpsExpr b (rename s) (\res5 -> cpsExpr c (rename s) (\res6 -> cpsExpr d (rename s) (\res7 -> App (cpsExpr fn s (\name -> name)) [res1, res2, res3, res4, res5, res6, res7, Lambda [newName (rename s) "result"] (context (Var (newName (rename s) "result")))])))))))

-- if expressions
cpsExpr (If cond conseq altern) s context = cpsExpr cond (rename s) (\result1 ->
    (If result1 
    (cpsExpr conseq (rename (rename s)) context)
    (cpsExpr altern (rename (rename (rename s))) context)))

--cpsExpr (If cond conseq altern) s context = cpsExpr cond s (\result1 -> cpsExpr conseq s (\result2 -> cpsExpr altern s (\result3 -> 
 --   context (If result1 result2 result3))))


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

prop_testCpsExprEqual :: Bool
prop_testCpsExprEqual = result == F
    where bindings = cpsDef [("n", Literal $ Num 2),
                             ("m", (Equal (Var "n") (Literal $ Num 3)))]
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
prop_testCpsExprFib = result == Num 8
    where bindings = cpsDef [("fib", Lambda ["n"]
                                (If (Equal (Var "n") (Literal (Num 0)))
                                    (Literal (Num 0))
                                    (If (Equal (Var "n") (Literal (Num 1)))
                                        (Literal (Num 1))
                                        (Plus (App (Var "fib") [(Plus (Var "n") (Literal (Num (-1))))]) 
                                        (App (Var "fib") [(Plus (Var "n") (Literal (Num (-2))))])))))]

          env = def bindings
          result = eval env $ (App (Var "cps_fib") [Literal $ Num 6, identityFn])

prop_testCPSIf :: Bool
prop_testCPSIf = result == F
    where bindings = cpsDef [("if", (If (Equal (Literal $ Num 1) (Literal $ Num 0)) (Literal $ T) (Literal $ F)))]
          env = def bindings
          result = eval env $ Var ("cps_if")

prop_testCPSExprIf :: Bool
prop_testCPSExprIf = result == F
    where bindings = cpsDef [("if", (If (Equal (Literal $ Num 0) (Literal $ Num 0)) (Equal (Literal $ Num 1) (Literal $ Num 2)) (Plus (Literal $ Num 1) (Literal $ Num 2))))]
          env = def bindings
          result = eval env $ Var ("cps_if")

prop_testCPSExprIf2 :: Bool
prop_testCPSExprIf2 = result == T
    where bindings = cpsDef [("n", Literal $ Num 2), ("if", (If (Equal (Var "n") (Literal $ Num 2)) (Literal $ T) (Literal $ F)))]
          env = def bindings
          result = eval env $ Var ("cps_if")

prop_testCPSNestedIf :: Bool
prop_testCPSNestedIf = result == T
    where bindings = cpsDef [("if", (If (Equal (If (Equal (Literal $ Num 0) (Literal $ Num 0)) (Literal $ Num 1) (Literal $ Num 2))
                                (Literal $ Num 1)) (Literal $ T) (Literal $ F)))]
          env = def bindings
          result = eval env $ Var ("cps_if")

prop_testCPSNestedIf2 :: Bool
prop_testCPSNestedIf2 = result == T
    where bindings = cpsDef [("if", (If (Equal (If (Equal (Literal $ Num 0) (Literal $ Num 0)) (Literal $ Num 1) (Literal $ Num 2))
                                (If (Literal $ F) (Literal $ Num 2) (Literal $ Num 1))) 
                                (Literal $ T) (Literal $ F)))]
          env = def bindings
          result = eval env $ Var ("cps_if")

prop_testCPSSimpleIf :: Bool
prop_testCPSSimpleIf = result == Num 0
    where bindings = cpsDef [("if",(If (Literal $ T) (Literal $ Num 0) (Literal $ Num 1)))]
          env = def bindings
          result = eval env $ Var ("cps_if")

prop_testCPSLambdaIf :: Bool
prop_testCPSLambdaIf = result == Num 4
    where bindings = cpsDef [("if",Lambda ["n"]
                                (If (Equal (Var "n") (Literal $ Num 0))
                                    (Literal $ Num 1)
                                    (Times (Var "n") (If (Equal (Var "n") (Literal $ Num 2)) (Var "n") (Literal $ Num 0)))))]
          env = def bindings
          result = eval env $ (App (Var "cps_if") [Literal $ Num 2, identityFn])

prop_testBasicApp :: Bool
prop_testBasicApp = result == Num 2
    where bindings = cpsDef [("p", Lambda ["n"] (Plus (Var "n")(Var "n"))), 
                                ("app", App (Var "p") [(Literal $ Num 1)])]
          env = def bindings
          result = eval env $ (Var "cps_app")

prop_testCPSBasicLambda :: Bool
prop_testCPSBasicLambda = result == Num 2
    where bindings = cpsDef [("lambda", Lambda ["n"] (Var "n"))]
          env = def bindings
          result = eval env $ (App (Var "cps_lambda") [Literal $ Num 2, identityFn]) 

prop_testCPSBasicLambda2 :: Bool
prop_testCPSBasicLambda2 = result == Num 4
    where bindings = cpsDef [("lambda", Lambda ["n"] 
                                (Plus (Var "n") (Var "n")))]
          env = def bindings
          result = eval env $ (App (Var "cps_lambda") [Literal $ Num 2, identityFn]) 

prop_testCPSNestedLambda :: Bool
prop_testCPSNestedLambda = result == Num 4
    where bindings = cpsDef [("lambda", Lambda ["n"] (Lambda ["m"] (Plus (Var "n") (Var "m"))))]
          env = def bindings
          result = eval env $ (App (App (Var "cps_lambda") [Literal $ Num 2, identityFn]) [Literal $ Num 2, identityFn])

prop_testCPSNestedLambda2 :: Bool
prop_testCPSNestedLambda2 = result == Num 4
    where bindings = cpsDef [("lambda", Lambda ["n", "m"] (Plus (Var "n") (Var "m")))]
          env = def bindings
          result = eval env $ (App (Var "cps_lambda") [Literal $ Num 2, Literal $ Num 2, identityFn])

prop_testCPSExprLambda :: Bool
prop_testCPSExprLambda = result == Num 4
    where bindings = cpsDef [("app", App (Lambda ["a"] (Plus (Var "a") (Var "a"))) [Literal $ Num 2])]
          env = def bindings
          result = eval env $ (Var "cps_app")

prop_testCPSExprLambda2 :: Bool
prop_testCPSExprLambda2 = result == Num 4
    where bindings = cpsDef [("app", App (Lambda ["a"] (App (Lambda ["b"] (Plus (Var "a") (Var "b"))) 
                                [Literal $ Num 2])) [Literal $ Num 2])]
          env = def bindings
          result = eval env $ (Var "cps_app")

prop_testCPSMultipleLambda :: Bool
prop_testCPSMultipleLambda = result == Num 7
    where bindings = cpsDef [("lambda", Lambda ["a","b","c","d","e","f","g"] 
                                (Plus (Var "a") (Plus (Var "b") (Plus (Var "c") (Plus (Var "d") (Plus (Var "e") (Plus (Var "f") (Var "g"))))))))]
          env = def bindings
          result = eval env $ (App (Var "cps_lambda") [Literal $ Num 1, Literal $ Num 1, Literal $ Num 1, Literal $ Num 1, Literal $ Num 1, Literal $ Num 1, Literal $ Num 1, identityFn])

prop_testCPSMApp3 :: Bool
prop_testCPSMApp3 = result == Num 3
    where bindings = cpsDef [("lambda", Lambda ["e","f","g"] 
                                (Plus (Var "e") (Plus (Var "f") (Var "g")))),
                                ("app", App (Var "lambda") 
                                [Literal $ Num 1, Literal $ Num 1, Literal $ Num 1])]
          env = def bindings
          result = eval env $ (Var "cps_app")

prop_testCPSMApp4 :: Bool
prop_testCPSMApp4 = result == Num 4
    where bindings = cpsDef [("lambda", Lambda ["d","e","f","g"] 
                                (Plus (Var "d") (Plus (Var "e") (Plus (Var "f") (Var "g"))))),
                                ("app", App (Var "lambda") 
                                [Literal $ Num 1, Literal $ Num 1, Literal $ Num 1, Literal $ Num 1])]
          env = def bindings
          result = eval env $ (Var "cps_app")

prop_testCPSMApp5 :: Bool
prop_testCPSMApp5 = result == Num 5
    where bindings = cpsDef [("lambda", Lambda ["c","d","e","f","g"] 
                                (Plus (Var "c") (Plus (Var "d") (Plus (Var "e") (Plus (Var "f") (Var "g")))))),
                                ("app", App (Var "lambda") 
                                [Literal $ Num 1, Literal $ Num 1, Literal $ Num 1, Literal $ Num 1, Literal $ Num 1])]
          env = def bindings
          result = eval env $ (Var "cps_app")

prop_testCPSMApp6 :: Bool
prop_testCPSMApp6 = result == Num 6
    where bindings = cpsDef [("lambda", Lambda ["b","c","d","e","f","g"] 
                                (Plus (Var "b") (Plus (Var "c") (Plus (Var "d") (Plus (Var "e") (Plus (Var "f") (Var "g"))))))),
                                ("app", App (Var "lambda") 
                                [Literal $ Num 1, Literal $ Num 1, Literal $ Num 1, Literal $ Num 1, Literal $ Num 1, Literal $ Num 1])]
          env = def bindings
          result = eval env $ (Var "cps_app")

prop_testCPSMApp7 :: Bool
prop_testCPSMApp7 = result == Num 7
    where bindings = cpsDef [("lambda", Lambda ["a","b","c","d","e","f","g"] 
                                (Plus (Var "a") (Plus (Var "b") (Plus (Var "c") (Plus (Var "d") (Plus (Var "e") (Plus (Var "f") (Var "g")))))))),
                                ("app", App (Var "lambda") 
                                [Literal $ Num 1, Literal $ Num 1, Literal $ Num 1, Literal $ Num 1, Literal $ Num 1, Literal $ Num 1, Literal $ Num 1])]
          env = def bindings
          result = eval env $ (Var "cps_app")

prop_testCPSAppLambda :: Bool
prop_testCPSAppLambda = result == Num 3
    where bindings = cpsDef [("b", Literal $ Num 2),("l", App (Lambda ["a"] (Plus (Literal $ Num 1) (Var "a")))  [Var "b"])]
          env = def bindings
          result = eval env $ (Var "cps_l")

prop_testCPSAppLambda2 :: Bool
prop_testCPSAppLambda2 = result == Num 4
    where bindings = cpsDef [("b", Literal $ Num 2),("l", App (Lambda ["a"] 
                                (Plus (App (Lambda ["c"] (Var "c")) [Var "b"]) (Var "a")))  [Var "b"])]
          env = def bindings
          result = eval env $ (Var "cps_l")
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
    quickCheck prop_testFib
    quickCheck prop_testCpsFib
    quickCheck prop_testCpsExprLiteral
    quickCheck prop_testCpsExprVar 
    quickCheck prop_testCpsExprPlus
    quickCheck prop_testCpsExprEqual
    quickCheck prop_testCpsExprFac 
    quickCheck prop_testCpsExprFib --Fails
    quickCheck prop_testCPSIf
    quickCheck prop_testCPSExprIf
    quickCheck prop_testCPSExprIf2
    quickCheck prop_testCPSNestedIf
    quickCheck prop_testCPSNestedIf2
    quickCheck prop_testCPSSimpleIf
    quickCheck prop_testCPSLambdaIf
    quickCheck prop_testBasicApp
    quickCheck prop_testCPSBasicLambda
    quickCheck prop_testCPSBasicLambda2
    quickCheck prop_testCPSNestedLambda
    quickCheck prop_testCPSNestedLambda2
    quickCheck prop_testCPSExprLambda
    quickCheck prop_testCPSExprLambda2
    quickCheck prop_testCPSMultipleLambda
    quickCheck prop_testCPSMApp3
    quickCheck prop_testCPSMApp4
    quickCheck prop_testCPSMApp5
    quickCheck prop_testCPSMApp6
    quickCheck prop_testCPSMApp7
    quickCheck prop_testCPSAppLambda
    quickCheck prop_testCPSAppLambda2
