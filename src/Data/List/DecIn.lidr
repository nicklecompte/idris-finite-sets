> module List.DecIn
> import Data.List
> %access public export

A type can have decidable list membership:

> ||| Decision procedures for determining list membership.
> interface DecIn (t: Type) where
>     decIn: (x:t) -> (xs : List t) -> Dec (Elem x xs)

Decidable equality and decidable list membership are equivalent. The first half
of the proof is quite easy - if we have decidable list membership, then 
deciding $x=y$ can be solved by determining $`DecIn` x [y]$.

> ||| Given an implementation of DecIn t, t has decidable equality.
> ||| Note: the implementation must be named due to a bug in Idris 1,
> ||| see (#4296)[https://github.com/idris-lang/Idris-dev/issues/4296]
> [decInToDecEqImpl] DecIn t => DecEq t where
>       decEq x y = case (decIn x [y]) of
>                        Yes Here => Yes Refl
>                        No contra => No (\eq => contra (rewrite eq in Here))

For the second half of the equivalence, we will need a trivial helper lemmas:

> matchingSingleton : Data.List.Elem x [y] -> (x = y)
> matchingSingleton Here = Refl
> matchingSingleton (There later) impossible

Using this, proving decidable equality gives decidable list memership is a bit
intricate, but mostly straightforward. The small difficulty arises from the fact
that, when deciding list membership, we traverse the list head-to-tail, but the
Idris prelude `Elem` goes from tail-to-head (building up `There` and `Here` 
calls). So we will need to make a recursive call on the tail of the list.

Note: perhaps this can be cleaned up a bit, it seems rather circuitous. 

> DecEq t => DecIn t where
>   decIn x [] = No absurd
>   decIn x (y::ys) with (decIn x ys) 
>       decIn x (y::ys) | No notLater = case decEq x y of
>           Yes Refl => Yes Here
>           No contra => No (\later => 
>                           case later of
>                               Here => contra (matchingSingleton Here)
>                               (There t) => notLater t)
>       decIn x (y::ys) | Yes later = Yes (There later)

> ElementPreservingCorrespondence : DecIn t => List t -> List t -> Type
> ElementPreservingCorrespondence xs ys = (x : t) -> (Elem x xs -> Elem x ys, Elem x ys -> Elem x xs)

> ||| ElementPreservingCorrespondence is a reflexive relation on lists.
> elementPreservingCorrespondenceReflexive : DecIn t => {xs : List t} -> ElementPreservingCorrespondence xs xs
> elementPreservingCorrespondenceReflexive {xs=[]} _ = (\a => absurd a, \b => absurd b)
> elementPreservingCorrespondenceReflexive {xs = (y::ys)} x = 
>   case decIn x (y::ys) of
>       Yes pf => (\a => pf,\b => pf)
>       No contra => (\a => absurd (contra a), \b => absurd (contra b))

> ||| ElementPreservingCorrespondence is a symmetric relation on lists.
> elementPreservingCorrespondenceSymmetric : DecIn t => {xs,ys : List t} -> ElementPreservingCorrespondence xs ys -> ElementPreservingCorrespondence ys xs
> elementPreservingCorrespondenceSymmetric pf x = (snd (pf x),fst (pf x))

> ||| ElementPreservingCorrespondence is a transitive relation on lists.
> elementPreservingCorrespondenceTransitive : 
>       DecIn t => {xs,ys,zs : List t} -> 
>       ElementPreservingCorrespondence xs ys -> 
>       ElementPreservingCorrespondence ys zs ->
>       ElementPreservingCorrespondence xs zs
> elementPreservingCorrespondenceTransitive pf1 pf2 x = 
>       ((fst (pf2 x)) . (fst (pf1 x)), (snd (pf1 x)) . (snd (pf2 x)))

