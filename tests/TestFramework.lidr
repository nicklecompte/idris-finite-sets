> module TestFramework
> %access export

> assertEq : Eq a => (testName : String) -> (given : a) -> (expected : a) -> IO ()
> assertEq testName g e = if g == e
>    then putStrLn (testName ++ "Passed")
>    else putStrLn (testName ++ "Failed")

> assertEqDetail : (Eq a, Show a) => (given : a) -> (expected : a) -> IO ()