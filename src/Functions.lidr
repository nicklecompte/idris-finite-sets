> module Functions
> %access public export

In this module we present types for basic proofs about functions between sets, such as

- injectivity, surjectivity, bijectivity
- quotienting by totality ("squashing")

> ||| The type of proofs that a given function is injective. 
> ||| A function `f: t -> u` is injective if, given a proof that `f x = f y`,
> ||| we can prove `x=y`. An implementation of `Injective f` is a function that
> ||| returns an `(x = y)` proof given an `(f x = f y)` proof.
> Injective : {t,u:Type} -> (t -> u) -> Type
> Injective f {t} = (x,y:t) -> (f x = f y) -> (x = y)

> ||| The type of proofs that a given function is surjective. 
> ||| A function `f: t -> u` is injective if, given any `y: u`, we can find 
> ||| `x: t` with a proof `f x = y`. An implementation of `Surjective f` is a 
> ||| function that returns a dependent pair `(x ** f x = y)`  given an 
> ||| `(f x = f y)` proof. Note that there is no proof of uniqueness.
> Surjective : {t,u:Type} -> (t -> u) -> Type
> Surjective f {t} {u} = (y:u) -> (x:t ** f x = y)

> ||| The type of proofs that a given function is bijective.
> ||| Since this is equivalent to being both injective and surjective, that is
> ||| the definition we are using. 
> Bijective : {t,u : Type} -> (t -> u) -> Type
> Bijective f {t} {u} = (Injective f, Surjective f)

> ||| The type of proofs that two types `t` and `u`, considered as simple sets 
> ||| built by their constructible members, have the same cardinality. For our 
> ||| purposes, this is equivalent to existential quantification on the type of
> ||| bijections between `t` and `u`.
> SameCardinality : Type -> Type -> Type
> SameCardinality t u = (f:(t->u) ** Bijective f)

Note that, for finite sets, the notion of `SameCardinality` collapses in the
obvious way; the problem of finding a bijection is equivalent to putting the 
elements of the sets into two lists with the same length. We will formally prove
this later.

> ||| Proof that a type is a "mere proposition" (i.e. it only has one inhabitant
> ||| up to decidable equality.)
> Prop : (t:Type) -> Type
> Prop t = (p1:t) -> (p2:t) -> (p1=p2)

If P is a decidable proposition, we can quotient P by the totality equivalence 
relation and get a "squashed" type. By "totality equivalence relation" we mean
a partition of the elements of $P : Type -> Type$ into two sets, one containing
constructible instances $P x$, the other containing unconstructible instances
$P y$. In NuPRL this is called "squash" so that is the name we will use here.

> squash : {p:Type} -> Dec p -> Type
> squash (Yes _) = Unit
> squash (No _) = Void

 Note that any two squashed values are trivially equal:

> ||| Any two squashed values of a given decidable proposition are equal.
> propSquash : {p: Type} -> (d : Dec p) -> Prop (squash d)
> propSquash (Yes prf) () () = Refl
> propSquash (No contra) v1 _ = absurd v1

> ||| Given a squashed proposition, obtain the original proposition.
> fromSquash : {p:Type} -> (d : Dec p) -> squash d -> p
> fromSquash (Yes prf) () = prf

Note that fromSquash can only ever accept a unit value since that is the only 
value that is constructible.

> ||| Simple helper for projecting the first part of a dependent pair.
> proj1DP : (DPair a b) -> a
> proj1DP (x ** y) = x

> ||| Simple helper for projecting the second part of a dependent pair.
> proj2DP : (x : (DPair a b)) -> b (proj1DP x)
> proj2DP (x ** y) = y