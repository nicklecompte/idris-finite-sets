> module Permutation
> import Data.List
> import Data.List.DecIn

> ||| Proofs that two lists `xs` and `ys` have the same length and same elements;
> ||| i.e., that `xs` and `ys` are related by a permutation of their elements.
> Permutation : DecIn t => List t -> List t -> Type
> Permutation xs ys = 
>   ((length xs = length ys),ElementPreservingCorrespondence xs ys)