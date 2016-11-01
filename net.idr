import Data.Vect
import Data.Fin

-- multiset over some type
MS : Type -> Type
MS a = a -> Nat

-- list of terms with equality to multiset conversion
toMS : Eq a => List a -> MS a
toMS [] = \_ => 0
toMS xs = \x => List.length $ filter (==x) xs

Tr : Nat -> Type
Tr s = (m, m) where m = List (Fin s)

initial : Tr s -> Bool
initial = ([]==) . fst

terminal : Tr s -> Bool
terminal = (==[]) . snd

Net : Nat -> Nat -> Type
Net s t = Vect t (Tr s)

Marking : Nat -> Type
Marking s = List (Fin s)

_dropM : Fin s -> Marking s -> Maybe (Marking s)
_dropM e m = toMaybe (List.elem e m) (List.delete e m)

consume : Marking s -> Marking s -> Maybe (Marking s)
consume [] m = Just m
consume (x :: xs) m = case _dropM x m of
  Nothing => Nothing
  Just m' => consume xs m'

produce : Marking s -> Marking s -> Maybe (Marking s)
produce x m = Just (m ++ x)

apTr : Tr s -> Marking s -> Maybe (Marking s)
apTr t m = do
  m' <- consume (fst t) m
  m'' <- produce (snd t) m'
  return m''

trMark : Net s t -> Fin t -> Marking s -> Maybe (Marking s)
trMark net t = apTr $ index t net

data Inst : Nat -> Nat -> Type where
  Init : Net s t -> Fin t -> Inst s t
  Fire : Inst s t -> Fin t -> Inst s t

-- -- proof that t is enabled for m
-- data Enabled : (t: Tr s) -> (m: Marking s) -> Type where
--   EnE : Enabled (List.Nil, _) _

iNet : Inst s t -> Net s t
iNet (Init net _) = net
iNet (Fire i _) = iNet i

marking : Inst s t -> Maybe (Marking s)
marking (Init net tr) = trMark net tr []
marking (Fire inst tr) = let net = iNet inst in do
  m <- marking inst
  trMark net tr m

net : Net 4 4
net = [
  ([], [0, 1]),
  ([0], [2]),
  ([1], [3]),
  ([2,3], [])
]

i0 : Inst 4 4
i0 = Init net 0

i1 : Inst 4 4
i1 = Fire i0 1

-- m0 : Marking 4
-- m0 = marking i0
