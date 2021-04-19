> module Data.Fin.Extensions
> import Data.Fin
> import Data.List
> import Data.List.TypeEnumeration

> embedNatAsFin : (n : Nat) -> (m : Nat) -> {pf: LT m n} -> Fin n
> embedNatAsFin Z _ {pf=_} impossible
> embedNatAsFin (S _) Z {pf = _} = FZ
> embedNatAsFin (S j) (S k) {pf = LTESucc x} = FS (embedNatAsFin j k {pf=x})

> Uninhabited (LT (S j) (S Z)) where
>    uninhabited (LTESucc x) = uninhabited x
 
> getLesserFins : {n:Nat} -> (f : Fin (S n)) -> List (Fin (S n))
> getLesserFins FZ = FZ :: []
> getLesserFins (FS x) = (FS x) :: (getLesserFins (weaken x))


> getLesserFinsContains : (x : Fin (S k)) -> Elem x (getLesserFins (last {n = k}))
> getLesserFinsContains {k = Z} FZ = ?getLesserFinsContains_rhs_3
> getLesserFinsContains {k = Z} (FS x) impossible
> getLesserFinsContains {k = (S k)} x = ?getLesserFinsContains_rhs_2

> natToListFin' : (n : Nat) -> List (Fin (S n))
> natToListFin' t = natToListFinInternal t t {pf=lteRefl} where
>   natToListFinInternal : (k:Nat) -> (l : Nat) -> {auto pf: LT (k) (S l)} -> List (Fin (S l))
>   natToListFinInternal Z Z {pf = _}= [FZ]
>   natToListFinInternal (S j) Z {pf} = absurd (uninhabited pf)
>   natToListFinInternal (S j) m {pf} = 
>       let headVal = (embedNatAsFin (S m) (S j) {pf=pf}) in
>           let tailVal = natToListFinInternal j m {pf = (lteSuccLeft pf)} in
>               headVal :: tailVal


> safeStrengthen : (f : Fin (S n)) -> (contra : (f = last {n=n}) -> Void) -> Fin n
> safeStrengthen {n=Z} FZ contra = absurd (contra Refl)
> safeStrengthen {n=(S k)} FZ contra = FZ
> safeStrengthen {n=(S k)} (FS x) contra = ?ssh_2

> natToListFinIsAll : (n : Nat) -> All (getLesserFins (last {n=n}))
> natToListFinIsAll Z =  ?isAll
> natToListFinIsAll (S k) = \f =>
>   case (decEq f (last {n=(S k)})) of
>       Yes pf => ?isAll1
>       No contra => ?isAll2
