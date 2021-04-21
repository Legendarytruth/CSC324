{- CSC324 Fall 2019: Exercise 9

*Before starting, please review the exercise guidelines at
https://www.cs.toronto.edu/~lczhang/324/homework.html*
-}
module Ex9 (typeCheck) where

-- This is one of Haskell's built-in analogues of dictionaries.
-- You may want to read up on the available functions here:
-- https://hackage.haskell.org/package/containers-0.4.2.0/docs/Data-Map.html
import qualified Data.Map as Map

-- | Import the types used for this exercise
import Ex9Types (Type(..), Formula(..), TypeEnv, Formulas)

-- | Imports used for testing purposes only.
import Control.Monad (liftM, liftM2)
import Test.QuickCheck (
    Property, quickCheck, oneof, sized, Arbitrary(..)
    )

------------------------------------------------------------------------------
-- Example Formula from the handout
------------------------------------------------------------------------------

exampleTypeEnv :: TypeEnv
exampleTypeEnv = Map.fromList [
    ("first_name", StrCol),
    ("last_name", StrCol),
    ("full_name", StrCol)]

exampleFormulas :: Formulas
exampleFormulas = Map.fromList [
    ("first_name", Nothing),
    ("last_name", Nothing),
    ("full_name", Just (Concat (Column "first_name") (Column "last_name")))]

------------------------------------------------------------------------------
-- Task 1: Type Checking
------------------------------------------------------------------------------

-- | This is the core type-checking function.
--
-- We recommend using the `Map.foldlWithKey` function to iterate through
-- one of the Maps, and using `typeCheckFormula` as a helper function
-- to check each of the columns
typeCheck :: TypeEnv -> Formulas -> Bool
typeCheck tenv fs = undefined




-- | Helper function to check if a particular formula matches its type by:
--      * Checking if the formula return type matches the actual return type
--      * Checking if the formula's argument type matches what is in the TypeEnv
-- This helper function is not tested. You are welcome to use a different
-- implementation strategy and create your own helper functions.
typeCheckFormula :: Formula -> Type -> TypeEnv -> Bool
typeCheckFormula formula returnType typeEnv = 
    if (StrCol == returnType) then True else False

formulaType :: Formula -> TypeEnv -> Bool
formulaType formula typeEnv = 
    case formula of 
        formulaType(Concat x y) = StrCol
-- formulaType (Length x) = NumCol
-- formulaType (NumToString x) = StrCol
-- formulaType (Column x) = NumCol

lookups :: TypeEnv-> String -> Type
lookups map key =
    case (Map.lookup key map) of
        Just x -> x


{-
------------------------------------------------------------------------------
-- Sample Tests
------------------------------------------------------------------------------

prop_testTypeCheckFormula :: Bool
prop_testTypeCheckFormula = (typeCheckFormula (Length (Column "a"))
                                              NumCol
                                              (Map.fromList [("a", StrCol)]))

prop_testExamplePass :: Bool
prop_testExamplePass = typeCheck exampleTypeEnv exampleFormulas

prop_testExample2Fail :: Bool
prop_testExample2Fail = False == (typeCheck exampleTypeEnv2 exampleFormulas2)
    where exampleTypeEnv2 = Map.fromList [("a", StrCol),
                                          ("b", StrCol)]
          exampleFormulas2 = Map.fromList [("a", Nothing),
                                           ("b", Just (Length (Column "a")))]
prop_testExample3Pass :: Bool
prop_testExample3Pass = (typeCheck exampleTypeEnv3 exampleFormulas3)
    where exampleTypeEnv3 = Map.fromList [("a", StrCol),
                                          ("b", StrCol)]
          exampleFormulas3 = Map.fromList [("a", Nothing),
                                           ("b", Just (NumToString (Length (Column "a"))))]

-- This main function runs the quickcheck tests.
-- This gets executed when you compile and run this program. We'll talk about
-- "do" notation later in the course, but for now if you want to add your
-- own tests, just define them above, and add a new `quickcheck` line here.
main :: IO ()
main = do
    -- | uncomment if you are implementing the typeCheckFormula helper:
    -- quickCheck prop_testTypeCheckFormula
    quickCheck prop_testExamplePass 
    quickCheck prop_testExample2Fail
    quickCheck prop_testExample3Pass

-}