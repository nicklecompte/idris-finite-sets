> module Listable
> import Functions
> import Data.Fin
> import Data.List

First we start with considering the following problem: given a type $t$ and a 
list $xs \in \texttt{List} t$, how can we determine if $xs$ contains every 
element of $t$? If this were the case, we would be able to construct a
function $f_{xs} : (x:t) \rightarrow \texttt{Elem} x xs$.

> ||| Proofs that a given list contains all possible elements of a given type.
> All : {t : Type} -> List t -> Type 
> All xs {t} = (x:t) -> Elem x xs

There are some boilerplate and uninhabited trivialities to get out of the way. 

> ||| Given a type t and a proof of t, it is a contradiction to have a proof that
> ||| the empty list contains all elements of t.
> allNotEmpty : All {t} [] -> t -> Void
> allNotEmpty f x = absurd (f x)

> ||| If a type `t` is uninhabited, then the empty list contains all elements 
> ||| of that type.
> voidEmptyAll : Uninhabited t => All {t} []
> voidEmptyAll = \c => absurd c


Then a list containing all elements of $t$ with no duplicates is defined by

> ||| Proofs that a list contains  no duplicates.
> NoDupes : {t:Type} -> List t -> Type
> NoDupes {t} xs = (x:t) -> Prop (Elem x xs)

With this we can start working on proving if a given list uniquely contains all
elements of a given type. We start with some trivial helper lemmas:

> ||| If we know $x$ belongs to a list $xs$ then $x :: xs$ obviously contains
> ||| duplicate values (namely, $x$).
> noDupesInHeadLemma : Elem x xs -> NoDupes (x :: xs) -> Void
> noDupesInHeadLemma {x = x} {xs = []} _ _ impossible
> noDupesInHeadLemma {x} a b = hereIsNotThere (b x Here (There a))

If a type has decidable equality, then All and NoDupes are decidable.
We need a (somewhat metamathematical) lemma to start stating that any two
void values of the same type are equal (there are in fact zero of them - this
is just a wrapper for "void can prove anything")

> ||| Any two contradictions of the same type are identical.
> voidsAreEquivalent : {t: Type} -> (t -> Void) -> (a:t) -> (b:t) -> (a=b)
> voidsAreEquivalent f a b = void (f a)

> ||| Equivalent to `There` being an injective function.
> thereLemma2 : {a: Elem x xs} -> {b : Elem x xs} -> (There a = There b) -> a = b
> thereLemma2 {a = Here} {b = Here} pf = Refl
> thereLemma2 {a = Here} {b = (There _)} Refl impossible
> thereLemma2 {a = (There _)} {b = Here} Refl impossible
> thereLemma2 {a = (There x)} {b = (There x)} Refl = Refl

> ||| For fixed $y$, `There` is an injective function from `Elem x xs` to 
> ||| `Elem x (y :: xs)`.
> thereInjective : Injective There
> thereInjective x y = thereLemma2 {a=x} {b=y}


> ||| Given a list `xs` without duplicates, and an element `x` known not to be
> ||| contained in `xs`, then `x :: xs` also contains no duplicates.
> consNoDupes : DecEq t => {x : t} -> NoDupes {t} xs -> (Not (Elem x xs)) -> NoDupes (x :: xs)
> consNoDupes {x = x} noDupesSublist notIn y pf1 pf2 with (decEq x y)
>   consNoDupes {x = y} noDupesSublist notIn y Here Here | Yes pf = Refl
>   consNoDupes {x = y} noDupesSublist notIn y Here (There later) | Yes pf = 
>               absurd (notIn later)
>   consNoDupes {x = y} noDupesSublist notIn y (There later) Here | Yes pf = 
>               absurd (notIn later)
>   consNoDupes {x = x} noDupesSublist notIn y (There later) (There z) | Yes pf = 
>               absurd (notIn (rewrite pf in later)) 
>   consNoDupes {x = y} noDupesSublist notIn y Here Here | No contra = Refl
>   consNoDupes {x = y} noDupesSublist notIn y Here (There later) | No contra = 
>               absurd (notIn later)
>   consNoDupes {x = y} noDupesSublist notIn y (There later) Here | No contra = 
>               absurd (notIn later)
>   consNoDupes {x = x} noDupesSublist notIn y (There later) (There z) | No contra = 
>               let ndupes = (noDupesSublist y later z) in cong ndupes


> ||| If a nonempty list contains no duplicates, then its tail has no duplicates.
> dupeCons : NoDupes (x :: xs) -> NoDupes xs
> dupeCons dupeBiglist item pf1 pf2 = thereLemma2 (dupeBiglist item (There pf1) (There pf2))

> ||| If a type `t` has decidable equality, then `List t` has a decision 
> ||| procedure for determining if it contains any duplicates.
> deqEqToDupe : DecEq t => (xs:List t) -> Dec (NoDupes xs)
> deqEqToDupe [] = Yes (\a => (\b => (\c => (voidsAreEquivalent uninhabited b c))))
> deqEqToDupe (x :: xs) with (isElem x xs)
>   deqEqToDupe (x :: xs) | Yes pf = No (noDupesInHeadLemma pf)
>   deqEqToDupe (x :: xs) | No contra = case deqEqToDupe xs of
>       Yes noDupes => Yes (consNoDupes noDupes contra)
>       No areDupes => No (\c => areDupes (dupeCons c))

Now we turn to propoisitions about finiteness. We start with the well-known
Kuratowski finiteness, which we will call `Listable`: a type $t$ is Kuratowski 
finite if its elements can be put into a single list. That is, we can find a list
$xs$ satisfying $\texttt{All} \{t\} xs$.

> ||| Proofs that a type `t` can be completely enumerated by a list `xs`.
> ||| Alternatively, this is a definition of a finite type.
> Listable : (t : Type) -> Type
> Listable t = (xs ** (All {t} xs))

