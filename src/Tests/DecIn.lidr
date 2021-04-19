> module Tests.DecIn
> import Data.List
> import Data.List.DecIn
> %access export

Simple smoke test verifying that 

> smokeDecIn : IO ()
> smokeDecIn = case (decIn (S Z) [1,2,3]) of
>                   Yes Here => putStrLn "smokeDecIn test passed"
>                   Yes (There x) => putStrLn "smokeDecIn returned There"
>                   No contra => putStrLn "smokeDecIn returned No"