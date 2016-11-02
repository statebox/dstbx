-- finite ptnets
import Data.Vect
import Data.Fin
import Data.HVect

Marking : {s : Nat} -> Type
Marking {s} = List (Fin s)

||| Obtain marking (maybe) by removing an element
_dropM : Fin s -> Marking {s} -> Maybe (Marking {s})
_dropM e m = toMaybe (List.elem e m) (List.delete e m)

Transition : {s : Nat} -> Type
Transition {s} = (Marking {s}, Marking {s})

pre : {s:Nat} -> Transition {s} -> Marking {s}
pre = fst

post : {s:Nat} -> Transition {s} -> Marking {s}
post = snd

||| Type of bipartite graphs over finite partitions
Net : Nat -> Nat -> Type
Net s t = Vect t (Transition {s})

transition : Net s t -> Fin t -> Transition {s}
transition net t = index t net

consume : {s:Nat} -> Marking {s} -> Marking {s} -> Maybe (Marking {s})
consume [] m = Just m
consume (x :: xs) m = case _dropM x m of
  Nothing => Nothing
  Just m' => consume xs m'

produce : {s:Nat} -> Marking {s} -> Marking {s} -> Maybe (Marking {s})
produce x m = Just (m ++ x)

applyT : {s:Nat} -> Transition {s} -> Marking {s} -> Maybe (Marking {s})
applyT t m = do
  m' <- consume (fst t) m
  m'' <- produce (snd t) m'
  return m''

data Inst : Nat -> Nat -> Type where
  Init : Fin t -> Net s t -> Inst s t
  Fire : Fin t -> Inst s t -> Inst s t

net : Inst s t -> Net s t
net (Fire _ i) = net i
net (Init _ n) = n

act : Net s t -> Fin t -> Marking {s} -> Maybe (Marking {s})
act n t = applyT (transition n t)

marking : Inst s t -> Maybe (Marking {s})
marking ev = case ev of
  Init tr n => act n tr []
  Fire tr i => let n = net i in do
    m <- marking i
    act n tr m

NonEmpty : {k:Nat} -> Type -> Type
NonEmpty {k} a = Vect (S k) a

nemptyInd : NonEmpty a -> (a -> b -> b) -> (a -> b) -> b
nemptyInd xs ind base = case xs of
  (x :: []) => base x
  (x :: (y :: ys)) => ind x (nemptyInd (y :: ys) ind base)

Transitions : {k:Nat} -> {t:Nat} -> Type
Transitions {k} {t} = NonEmpty {k} (Fin t)

fire' : Net s t -> Transitions {k} {t} -> Inst s t
fire' n xs = nemptyInd xs ind base
  where
    -- ind : Fin t -> Inst s t -> Inst s t
    ind ti inst = Fire ti inst
    -- base : Fin t -> Inst s t
    base t0 = Init t0 n

fire : Net s t -> Transitions {k} {t} -> Inst s t
fire n trs = fire' n (reverse trs)

-- Some basic text rendering

showMarking : Marking -> String
showMarking [] = "void"
showMarking xs = show $ map finToNat xs

showInstance : Inst s t -> String
showInstance i = case marking i of
  Nothing => "invalid state"
  Just m => showMarking m

showMMarking : Maybe Marking -> String
showMMarking mayb = case mayb of
  Nothing => "nothing"
  Just m => showMarking m

showTransition : Transition -> String
showTransition (pre, post) = mi ++ "=>" ++ mo
  where
    mi = showMarking pre
    mo = showMarking post

showNet : Net s t -> String
showNet n = show $ map showTransition n


-- -- -- -- -- -- --
-- -- Examples! - --
-- -- -- -- -- -- --

net0 : Net 4 4
net0 = [
  ([], [0, 1]),
  ([0], [2]),
  ([1], [3]),
  ([2,3], [])
]

-- okay, need either heterogeneous vectors
-- or dependent pair approach
--
-- DVec : Nat -> Type -> Type
-- DVec k a = (k ** Vect k a)
--
-- toDVec : {k:Nat} -> {a:Type} -> Vect k a -> DVec k a
-- toDVec {k} xs = (k ** xs)
--
-- Trs : Nat -> Type
-- Trs s = DVec (Fin s)
--
-- fseqs : {Net s t} -> HVect (Vect k Type)
-- fseqs {s} {t} = map (map \x -> F) [
--   [0],
--   [0,1,3],
--   [0,1,2],
--   [0,1,2,3]
-- ]
--
-- main : IO ()
-- main = do
--   for fseqs (putStrLn . showInstance . fire net0)

-- fire n (ti :: tK) = Fire ti (fire n tK)
-- fire n (t0 :: []) = Init t0 n

-- i0 : Inst 4 4
-- i0 = Init 0 net
--
-- i1 : Inst 4 4
-- i1 = Fire 2 i0
