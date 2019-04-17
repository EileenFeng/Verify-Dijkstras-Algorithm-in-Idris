module Column
import Graph
import Data.Vect

%default total
%access public export


{- helper proofs on Elem type -}
elemEq : Elem a (b :: Nil) -> a = b
elemEq Here = Refl


elemRes : Elem a (x :: xs) -> Not (a = x) -> Elem a xs
elemRes Here neq = absurd (neq $ elemEq Here)
elemRes (There e) neq = e

{- insert middle -}
elem_insert_mid : (Elem a (x :: xs)) ->
              Elem a (x :: x' :: xs)
elem_insert_mid Here = Here
elem_insert_mid (There e) = There $ There e


{-------------------- Column Definition -------------------------}

data Column : (len : Nat) -> (g : Graph gsize weight ops) -> (src : Node gsize) -> Type where
  MKColumn : (g : Graph gsize weight ops) ->
             (src : Node gsize) ->
             (len : Nat) ->
             (unexp : Vect len (Node gsize)) ->
             (dist : Vect gsize (Distance weight)) ->
             Column len g src




CElem : {g : Graph gsize weight ops} ->
        (v : Node gsize) ->
        (cl : Column len g src) ->
        Type
CElem v (MKColumn _ _ _ unexp _) = Elem v unexp



-- get the dist from Column
cdist : {g : Graph gsize weight ops} ->
        (Column len g src) ->
        Vect gsize (Distance weight)
cdist (MKColumn _ _ _ _ dist) = dist


-- getDist from a node
looseIndex : Fin n -> Vect m a -> a -> a
looseIndex _ Nil deflt = deflt
looseIndex FZ (x :: _) _ = x
looseIndex (FS n') (_ :: xs) deflt = looseIndex n' xs deflt


looseIndexN : Nat -> Vect m a -> a -> a
looseIndexN Z (x :: xs) deflt = x
looseIndexN _ Nil deflt = deflt
looseIndexN (S n) (x :: xs) deflt = looseIndexN n xs deflt


indexN : (n : Nat) ->
         Vect m a ->
         {auto p : LT n m} ->
         a
indexN (S _) Nil {p} = absurd $ succNotLTEzero p
indexN Z (x :: xs) = x
indexN (S n) (x :: xs) {p=LTESucc p'} = indexN n xs {p=p'}


nodeDistN : {g : Graph gsize weight ops} ->
            (v : Node gsize) ->
            (cl : Column len g src) ->
            Distance weight
nodeDistN v cl = indexN (finToNat (getVal v)) (cdist cl) {p=nvLTE (getVal v)}



nodeDistL : {g : Graph gsize weight ops} ->
            (v : Node gsize) ->
            (cl : Column len g src) ->
            Distance weight
nodeDistL (MKNode nv) cl = looseIndexN (finToNat nv) (cdist cl) DInf



nodeDist : {g : Graph gsize weight ops} ->
           (v : Node gsize) ->
           (cl : Column len g src) ->
           Distance weight
nodeDist (MKNode nv) cl = indexN (finToNat $ nv) (cdist cl) {p=nvLTE nv}
--nodeDist v cl = index (getVal v) (cdist cl)

{- unexplored and explored nodes-}
unexplored : {g : Graph gsize weight ops} ->
             (v : Node gsize) ->
             (cl : Column len g src) ->
             Type
unexplored v cl = CElem v cl


explored : {g : Graph gsize weight ops} ->
           (v : Node gsize) ->
           (cl : Column len g src) ->
           Type
explored v cl = Not (CElem v cl)



checkUnexplored : {g : Graph gsize weight ops} ->
               (v : Node gsize) ->
               (cl : Column len g src) ->
               Dec (CElem v cl)
checkUnexplored v (MKColumn g src len unexp dist) = isElem v unexp



{- getMin from Column -}
getMinNode : (nodes : Vect (S len) (Node gsize)) ->
             (ops : WeightOps weight) ->
             (dist : Vect gsize (Distance weight)) ->
             Node gsize
getMinNode (x :: Nil) _ _ = x
getMinNode (x :: (y :: xs)) ops dist {gsize}
  = case (dgte ops (index (getVal x) dist) (index (getVal min) dist)) of
         True => min
         False => x
  where
    min : Node gsize
    min = getMinNode (y :: xs) ops dist

getMin : {g : Graph gsize weight ops} ->
         (cl : Column (S len) g src) ->
         (Node gsize)
getMin (MKColumn _ _ _ unexp dist) {ops} = getMinNode unexp ops dist



{- min is element of the Column-}
{- elem of nodes -}
minElem : (nodes : Vect (S len) (Node gsize)) ->
          (ops : WeightOps weight) ->
          (dist : Vect gsize (Distance weight)) ->
          Elem (getMinNode nodes ops dist) nodes
minElem (x :: Nil) _ _ = Here
minElem (x :: (y :: xs)) ops dist
  with (dgte ops (index (getVal x) dist)
                 (index (getVal $ getMinNode (y :: xs) ops dist) dist))
    | True = There $ minElem (y :: xs) ops dist
    | False = Here

minCElem : {g : Graph gsize weight ops} ->
           (cl : Column (S len) g src) ->
           (CElem (getMin cl) cl)
minCElem (MKColumn _ _ _ unexp dist) {ops} = minElem unexp ops dist


{- delete min from Column-}
{- deleteMin helper with nodes as input-}
deleteMinNode : (min : Node gsize) ->
                (nodes : Vect (S len) (Node gsize)) ->
                (p : Elem min nodes) ->
                Vect len (Node gsize)
deleteMinNode x (x :: xs) Here = xs
deleteMinNode min (x :: Nil) (There e) = absurd $ noEmptyElem e
deleteMinNode min (x :: (x' :: xs)) (There e) = x :: (deleteMinNode min (x' :: xs) e)



deleteMin : {g : Graph gsize weight ops} ->
            (cl : Column (S len) g src) ->
            Column len g src
deleteMin cl@(MKColumn g src (S len) unexp dist)
  = MKColumn g src len (deleteMinNode (getMin cl) unexp (minCElem cl)) dist



deleteMinElem : (min : Node gsize) ->
                (v : Node gsize) ->
                (nodes : Vect (S len) (Node gsize)) ->
                (p : Elem min nodes) ->
                (e : Elem v (deleteMinNode min nodes p)) ->
                Elem v nodes
deleteMinElem min v (_ :: xs) Here e = There e
deleteMinElem min v (_ :: (x :: xs)) (There later) Here = Here
deleteMinElem min v (_ :: (x' :: xs)) (There pe) (There e) = There $ deleteMinElem min v (x' :: xs) pe e





deleteNElem : (min : Node gsize) ->
              (v : Node gsize) ->
              (nodes : Vect (S len) (Node gsize)) ->
              (p : Elem min nodes) ->
              (ne : Not (Elem v nodes)) ->
              Not (Elem v (deleteMinNode min nodes p))
deleteNElem min v (_ :: xs) Here nev ev with (v == min) proof minIsV
  | True = absurd $ nev (rewrite (nodeEq {a=v} {b=min} $ sym minIsV) in Here)
  | False = nev (There ev)
deleteNElem min v (x :: (x' :: xs)) (There pe) nev ev with (v == min) proof minIsV
  | True = absurd $ nev (There (rewrite (nodeEq {a=v} {b=min} $ sym minIsV) in pe))
  | False with (v == x) proof vIsx
    | True = absurd $ nev (rewrite (nodeEq {a=v} {b=x} $ sym vIsx) in Here)
    | False = absurd $ nev (deleteMinElem min v (x :: (x' :: xs)) (There pe) ev)



deleteNElemRev : (min : Node gsize) ->
                 (v : Node gsize) ->
                 (nodes : Vect (S len) (Node gsize)) ->
                 (p : Elem min nodes) ->
                 (ne : Not (Elem v (deleteMinNode min nodes p))) ->
                 (notMin : Not (min = v)) ->
                 Not (Elem v nodes)
deleteNElemRev min v (_ :: xs) Here ne notMin (There e) = absurd $ ne e
deleteNElemRev _ _ (_ :: xs) Here _ notMin Here = absurd $ notMin Refl
deleteNElemRev min v (v :: (x' :: xs)) (There em) ne notMin Here = absurd $ ne Here
deleteNElemRev min v (x :: (x' :: xs)) (There em) ne notMin (There ve)
  with (isElem v (deleteMinNode min (x' :: xs) em)) proof vIsElem
    | Yes ye = absurd $ ne (There ye)
    | No noe = deleteNElemRev min v (x' :: xs) em noe notMin ve




{- proof of getMin indeed gets the min node -}

minNodes : (nodes : Vect (S len) (Node gsize)) ->
           (ops : WeightOps weight) ->
           (dist : Vect gsize (Distance weight)) ->
           (p : Elem x nodes) ->
           (dgte ops (index (getVal x) dist)
                     (index (getVal $ getMinNode nodes ops dist) dist)) = True
minNodes (x :: Nil) _ _ p = rewrite (elemEq p) in dgteRefl
minNodes (x :: (y :: xs)) ops dist Here
  with (dgte ops (index (getVal x) dist)
                 (index (getVal $ getMinNode (y :: xs) ops dist) dist)) proof min_here
    | True = sym min_here
    | False = dgteRefl
minNodes (x :: (y :: xs)) ops dist (There e)
  with (dgte ops (index (getVal x) dist)
                 (index (getVal $ getMinNode (y :: xs) ops dist) dist)) proof xMin
    | True  = minNodes (y :: xs) ops dist e
    | False = dgteComm (minNodes (y :: xs) ops dist e) (dgteReverse $ sym xMin)




indexEq : (dist : Vect gsize (Distance weight)) ->
          (x : Node gsize) ->
          index (getVal x) dist = indexN (finToNat (getVal x)) dist {p=nvLTE $ getVal x}
indexEq Nil x = absurd $ NodeZAbsurd x
indexEq (d :: ds) (MKNode FZ) = Refl
indexEq (d :: ds) (MKNode (FS f)) = indexEq ds (MKNode f)


minCl : {g : Graph gsize weight ops} ->
        (cl : Column (S len) g src) ->
        (v : Node gsize) ->
        (ve : CElem v cl) ->
        dgte ops (nodeDistN v cl)
                 (nodeDistN (getMin cl) cl) = True
minCl (MKColumn g src (S len) unexp dist) v ve {ops}
  = rewrite (sym $ indexEq dist v) in
        (rewrite (sym $ indexEq dist (getMinNode unexp ops dist)) in (minNodes unexp ops dist ve))





{- helper proofs for Dijkstra's -}
lte_refl : (a : Nat) -> (lte a a = True)
lte_refl Z = Refl
lte_refl (S n) = lte_refl n


lte_succ_refl : (lte (S a) b = True) ->
                (lte a b = True)
lte_succ_refl {a=Z} {b=Z} refl = absurd $ trueNotFalse (sym refl)
lte_succ_refl {a=Z} {b=S b'} refl = refl
lte_succ_refl {a=S _} {b=Z} refl = absurd $ trueNotFalse (sym refl)
lte_succ_refl {a=S a'} {b=S b'} refl = lte_succ_refl {a=a'} {b=b'} refl




bnot : (f = False) -> Not (f = True)
bnot rt rf = absurd $ contradict rf rt

{- proof of minus zero-}
minusZ : minus a Z = a
minusZ {a=Z} = Refl
minusZ {a=S a'} = Refl

{- proof of minusRefl -}
minusRefl : minus a a = Z
minusRefl {a=Z} = Refl
minusRefl {a=S a'} = minusRefl {a=a'}


-- minusInj : minus a b = minus (S a) (S b)


-- LTE proofs
lteMinus : (gsize, n : Nat) ->
           (p : LTE (S n) gsize) ->
           LT (minus gsize (S n)) gsize
lteMinus Z _ LTEZero impossible
lteMinus (S g) Z p = rewrite (minusZ {a=g}) in lteRefl
lteMinus (S g) (S n) (LTESucc p) = lteSuccRight $ lteMinus g n p



{-proof of plusSuccRight-}
plusSuccRight : (a : Nat) -> (b : Nat) -> S (plus a b) = plus a (S b)
plusSuccRight Z Z = Refl
plusSuccRight Z (S b) = Refl
plusSuccRight (S a) b = cong $ plusSuccRight a b



{- converting nat to Fin without maybe -}
natTofin : (m : Nat) -> (n : Nat) -> {auto p : LT m n} -> Fin n
natTofin Z (S n) = FZ
natTofin (S m) (S n) {p = LTESucc _} = FS $ natTofin m n




{- get the third element from tuple-}
third : (a, a, a) -> a
third (a1, a2, a3) = a3

{- proof of minusSuccLeft -}
minusSuccLeft : (g : Nat) ->
            (c : Nat) ->
            (p : LTE c g) ->
            S (minus (S g) (S c)) = minus (S g) c
minusSuccLeft Z Z p = Refl
minusSuccLeft (S g) Z p = Refl
minusSuccLeft (S g) (S c) p = minusSuccLeft g c $ fromLteSucc p



{- helper for making list of nodes: initial input to dijkstra's -}
mknodes : (gsize : Nat) ->
          (cur : Nat) ->
          (p : LTE cur gsize) ->
          (Vect (minus gsize cur) (Node gsize)) ->
          (Vect gsize (Node gsize))
mknodes Z Z p vec = Nil
mknodes Z (S c) p vec = absurd p
mknodes (S g) Z p vec = vec
mknodes (S g) (S c) p vec
  = mknodes (S g) c (lteSuccLeft p)
            $ rewrite (sym $ minusSuccLeft g c (fromLteSucc p)) in ((MKNode $ natTofin c (S g)) :: vec)


mkNodes : (gsize : Nat) ->
          Vect gsize (Node gsize)
mkNodes gsize
  = mknodes gsize gsize lteRefl (rewrite (minusRefl {a=gsize}) in Nil)


{- helper for making list of initial distance values-}

allDInf : (gsize : Nat) ->
          (weight : Type) ->
          Vect gsize (Distance weight)
allDInf Z _ = Nil
allDInf (S n') w = DInf :: (allDInf n' w)



mkdists : (gsize : Nat) ->
          (src : Node gsize) ->
          (ops : WeightOps weight) ->
          Vect gsize (Distance weight)
mkdists Z _ _ = Nil
mkdists gsize (MKNode sv) ops {weight}
  = replaceAt sv (DVal $ zero ops) (allDInf gsize weight)




mkNodeEq : {gsize : Nat} ->
           (nf : Fin gsize) ->
           MKNode nf = (indexN (finToNat nf) (mkNodes gsize) {p=nvLTE nf})
mkNodeEq {gsize=Z} f = absurd $ FinZAbsurd f
mkNodeEq {gsize=S len} f = ?meq



indexClEq : {g : Graph gsize weight ops} ->
            (cl : Column len g src) ->
            (v, u : Node gsize) ->
            (eq : v = u) ->
            nodeDistN u cl = nodeDistN v cl
indexClEq cl v u eq = rewrite eq in Refl


{-
nDInfIsSrc : {g : Graph gsize wieght ops} ->
             {v, src : Node gsize} ->
             (ne : dgte ops (indexN (finToNat (getVal v)) (mkdists gsize src ops) {p=nvLTE $ getVal v}) DInf = False) ->
             v = src
-}

{-
index_mkNodesEq : {gsize : Nat} ->
                  (w : Node gsize) ->
                  w = indexN (finToNat (getVal w)) (mkNodes gsize) {p=nvLTE $ getVal w}
-}
