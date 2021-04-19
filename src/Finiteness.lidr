> module Listable
> import Functions
> import Data.Fin
> import Data.List
> import Data.List.TypeEnumeration
> import Data.Fin.Extensions


Now we turn to propositions about finiteness. We start with the well-known
Kuratowski finiteness, which we will call `Listable`: a type $t$ is Kuratowski 
finite if its elements can be put into a single list. That is, we can find a list
$xs$ satisfying $\texttt{All} \{t\} xs$.

> ||| Proofs that a type `t` can be completely enumerated by a list `xs`.
> ||| Alternatively, this is a definition of a finite type.
> Listable : (t : Type) -> Type
> Listable t = (xs ** (All {t} xs))

An alternative idea is to require a surjection Fin n to t for some Nat n:

> FinSurjective : (t: Type) -> Type
> FinSurjective ty = (n:Nat ** (fromFin : (Fin n -> ty) ** (Surjective fromFin)))

These notions are equivalent. We need some helper lemmas... it is quite likely 
that these can be cleaned up considerably...

> ||| If we have a proof that `x` is contained in the list `xs`, then we can map
> ||| that proof to a `Fin (length xs)` in the obvious way.
> getIndexOfElem : Elem x xs -> Fin (length xs)
> getIndexOfElem Here = FZ
> getIndexOfElem (There later) = FS (getIndexOfElem later)

> ||| Given a proof that some `xs : List t` contains all instances of type `t`,
> ||| get the `Fin (length xs)`-valued index of any `x : t`. 
> getIndexFromAll : All {t} xs -> t -> Fin (length xs)
> getIndexFromAll {xs = []} pf x = absurd (pf x)
> getIndexFromAll {xs = (y :: xs)} pf x = getIndexOfElem (pf x)

> ||| Index into a list `l` with a `Fin (length l).`
> finIndexList : (l:List t) -> Fin (length l) -> t
> finIndexList [] _ impossible
> finIndexList (x :: _) FZ = x
> finIndexList (_ :: xs) (FS y) = finIndexList xs y

> getIndexOfElemLemma : (pf : Elem x xs) -> finIndexList xs (getIndexOfElem pf) = x
> getIndexOfElemLemma {xs = (x :: ys)} Here = Refl
> getIndexOfElemLemma {xs = (y :: ys)} (There later) = getIndexOfElemLemma later

> getIndexOfAllLemma : (pf : All {t} xs) -> (x : t) -> finIndexList xs (getIndexFromAll pf x) = x
> getIndexOfAllLemma {xs} pf x with (pf x)
>   getIndexOfAllLemma {xs= x :: ys} pf x | Here = getIndexOfElemLemma (pf x)
>   getIndexOfAllLemma {xs= y :: ys} pf x | (There later) = getIndexOfElemLemma (pf x)

> finIndexListSurjectiveIfAll : All {t} xs -> Surjective (finIndexList xs)
> finIndexListSurjectiveIfAll {xs} pf = \y => ((getIndexFromAll pf y) ** (getIndexOfAllLemma pf y))

> indexIntoAll : All {t} xs -> (f : (Fin (length xs) -> t) ** Surjective f)
> indexIntoAll {xs} pf = ((finIndexList xs) ** (finIndexListSurjectiveIfAll pf))
> listableIsFinSurjective : Listable t -> FinSurjective t
> listableIsFinSurjective (xs ** pf) = ((length xs) ** (indexIntoAll pf))


> elemToFinIndex : {t : Type} -> (x:t  ** Elem x xs) -> Fin (length xs)
> elemToFinIndex (_ ** Here) = FZ
> elemToFinIndex ( x ** (There later)) = FS (elemToFinIndex (x ** later))

> proj1DP : (DPair a b) -> a
> proj1DP (x ** y) = x

> proj2DP : (x : (DPair a b)) -> b (proj1DP x)
> proj2DP (x ** y) = y

> elemLemma : {y: t} -> (x ** Data.List.Elem x xs) -> (x ** Data.List.Elem x (y :: xs))
> elemLemma (a ** pf) = (a ** (Data.List.There pf))

> finIndexToElem : (xs : List t) -> (index : Fin (length xs)) -> (x : t ** (Elem x xs))
> finIndexToElem [] _ impossible
> finIndexToElem (x :: xs) FZ = (x ** Here)
> finIndexToElem (b :: bs) (FS j) = elemLemma {y=b} (finIndexToElem bs j)

> elemLemmaLemma : {y:t} -> {xs : List t} -> {e : (x ** Data.List.Elem x xs)} -> (elemToFinIndex e = m) -> (elemToFinIndex (elemLemma e) = FS m)
> elemLemmaLemma {y = y} {e = (x ** pf)} Refl = Refl


> elemToFinIndexLemma : (x : t) -> (xs : List t) -> (y : Fin (length xs)) -> 
>                       (subres2 : elemToFinIndex (finIndexToElem xs y) = y) -> 
>                       elemToFinIndex (elemLemma (finIndexToElem xs y)) = FS y
> elemToFinIndexLemma x [] y _ impossible
> elemToFinIndexLemma x (z :: xs) y subres2 = elemLemmaLemma {y=z} {xs=(z::xs)} {e=(finIndexToElem(z::xs) y)} subres2 

> finIndexElemInverse1 : (xs : List t) -> (index : Fin (length xs)) -> (elemToFinIndex (finIndexToElem xs index) = index)
> finIndexElemInverse1 [] _ impossible
> finIndexElemInverse1 (x :: xs) FZ = Refl
> finIndexElemInverse1 (x :: xs) (FS y) = let subres2 = (finIndexElemInverse1 xs y) in (elemToFinIndexLemma x xs y subres2)


> finSurjectiveIsListable : FinSurjective t -> Listable t
> finSurjectiveIsListable (bound ** (surj ** pf)) = ?finSurjectiveIsListable_rhs_2

Listability gives an upper bound on the cardinality of any given type considered 
as sets. We can strengthen this by forbidding duplicates:

> ListableNoDuplicate : (t: Type) -> Type
> ListableNoDuplicate t = (xs : List t ** (All {t} xs, NoDupes {t} xs))

Alternatively, we can strengthen FinSurjectivity by requring a bijection:

> FinBijective : (t: Type) -> Type
> FinBijective t  = (n:Nat ** (f : (t -> Fin n) ** Bijective f))

These two notions are equivalent:

> finBijToListNoDupes : {t:Type} -> FinBijective t -> ListableNoDuplicate t

> listNoDupesToFinBij : {t:Type} -> ListableNoDuplicate t -> FinBijective t

Actually, all four notions of finiteness are equivalent. The reason is that 
listability implies decidable equality:

> listableToDecEq : {t:Type} -> Listable t -> (x: t) -> (y : t) -> Dec (x = y)
> listableToDecEq (xs **pf) x y = ?listableToDecEq_rhs
