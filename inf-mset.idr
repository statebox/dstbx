import Data.Vect
import Data.Fin

{-

categorically,

multisets are usually given by a carrier set "a"
and some function called the multiplicity, "a -> Nat".

While clean, this can be tricky to work with.
Why? Consider for instance equality of multisets,
this now becomes equality of functions.

a : Type

m0 : a -> Nat
m1 : a -> Nat

all_equal : (x:a) -> (m0 x) == (m1 x)

m0 == m1 <=> proof that all_equal is True for all x

If you have some way to enumerate all terms in
that type "a" this can be done, see below.

-}

-- multiset over some type
MS : Type -> Type
MS a = a -> Nat

-- list of terms with equality to multiset conversion
toMS : Eq a => List a -> MS a
toMS [] = \_ => 0
toMS xs = \x => List.length $ filter (==x) xs

FMS : Nat -> Type
FMS s = MS (Fin s)

ptEq : FMS s -> FMS s -> Fin s -> Bool
ptEq a b e = (a e) == (b e)

fSize : {a:Nat} -> Fin a -> Nat
fSize {a} _ = a

fElems' : (n:Nat) -> (a:Integer) -> List (Fin (S n))
fElems' n 0 = [0]
fElems' n x = [restrict n x] ++ (fElems' n (x - 1))

fElems : {a:Nat} -> List (Fin (S a))
fElems {a} = fElems' a (toIntegerNat a)

finPropAll : {n:Nat} -> (Fin (S n) -> Bool) -> List Bool
finPropAll p = map p fElems

fmsEq' : FMS (S s) -> FMS (S s) -> List Bool
fmsEq' f g = map (ptEq f g) fElems

fmsEq : {s:Nat} -> FMS s -> FMS s -> List Bool
fmsEq {s} f g = case s of
  Z => []
  S n => fmsEq' f g

Eq (FMS s) where
  (==) f g = foldl (&&) True (map Delay $ fmsEq f g)

ms0 : FMS 4
ms0 = toMS [0,1,2,2,3,2]

ms1 : FMS 4
ms1 = toMS [2,3,0,1,2,2]

isEmpty : FMS n -> Bool
isEmpty m = m == toMS []
