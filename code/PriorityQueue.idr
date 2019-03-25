module PriorityQueue
import Graph
import Data.Vect

%default total
%access public export

{-
  PriorityQueue of nodes from a given graph (key : node, value : Distance weight)
  sorted in ascending order of distance value
-}

{- `dist` holds the distance value for all nodes in the graph regardless of the number of nodes in the queue -}


{
  -- version 4: no pq just vec

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





{- get min node version2-}
{- getMinNode takes in nodes -}
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


{- min is element of the queue-}
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


{- delete min from queue-}

{- deleteMin helper with nodes as input-}
deleteMinNode : (min : Node gsize) ->
                  (nodes : Vect (S len) (Node gsize)) ->
                  (p : Elem min nodes) ->
                  Vect len (Node gsize)
deleteMinNode min (x :: Nil) p with (min == x) proof nil
  | True = Nil
  | False = absurd $ contradict (nodeEqReverse $ elemEq p) (sym nil)
deleteMinNode min (x :: (x' :: xs')) p with (min == x) proof cons
  | True  = x' :: xs'
  | False = x :: deleteMinNode min (x' :: xs') (elemRes p (nodeNeq (sym cons)))


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



--version 3



  {- This version of PQ does not keep the list of nodes sorted, but search for the minimum value during each iteration -}

data PriorityQueue : (gsize : Nat) -> (len : Nat) -> Type -> Type where
  MKQueue : (ops : WeightOps weight) ->
            (len : Nat) ->
            (nodes : Vect len (Node gsize)) ->
            (dist : Vect gsize (Distance weight)) ->
            PriorityQueue gsize len weight


{- check if a node is in priorityqueue -}
QElem : (target : Node gsize) ->
        (q : PriorityQueue gsize len weight) ->
        Type
QElem n (MKQueue _ _ nodes _) = Elem n nodes


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


{- get nodes from queue-}
qnodes : (q : PriorityQueue gsize len weight) ->
         (Vect len (Node gsize))
qnodes (MKQueue _ _ nodes _) = nodes


{- get ops from queue -}
qops : (q : PriorityQueue gsize len weight) ->
       WeightOps weight
qops (MKQueue ops _ _ _) = ops


{- get distance list of a queue-}
qdist : (q : PriorityQueue gsize len weight) ->
        (Vect gsize (Distance weight))
qdist (MKQueue _ _ _ dist) = dist



updateQDist : (q : PriorityQueue gsize len weight) ->
              (Vect gsize (Distance weight)) ->
              PriorityQueue gsize len weight
updateQDist (MKQueue ops len nodes dist) ndist = MKQueue ops len nodes ndist

{- get the distance of a specific node from priorityqueue-}
getNodeDist : (n : Node gsize) ->
              (q : PriorityQueue gsize len weight) ->
              Distance weight
getNodeDist n (MKQueue _ _ _ dist) = index (getVal n) dist


{- update the distance of a target node -}
updateNodeDist : (q : PriorityQueue gsize len weight) ->
                 (target : Node gsize) ->
                 (newd : Distance weight) ->
                 PriorityQueue gsize len weight
updateNodeDist (MKQueue ops len nodes dist) (MKNode tv) newd
  = MKQueue ops len nodes $ updateAt tv (\x => newd) dist



{- get min node version2-}
{- getMinNode takes in nodes -}
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

{- wrapper for pqueue-}
getMin : PriorityQueue gsize (S len) weight ->
         Node gsize
getMin (MKQueue ops (S len) nodes dist) = getMinNode nodes ops dist


{- min is element of the queue-}
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

{- wrapper for pqueue -}
minQElem : (q : PriorityQueue gsize (S len) weight) ->
           (QElem (getMin q) q)
minQElem (MKQueue ops (S len) nodes dist) = minElem nodes ops dist

{- delete min from queue-}

{- deleteMin helper with nodes as input-}
deleteMinHelper : (min : Node gsize) ->
                  (nodes : Vect (S len) (Node gsize)) ->
                  (p : Elem min nodes) ->
                  Vect len (Node gsize)
deleteMinHelper min (x :: Nil) p with (min == x) proof nil
  | True = Nil
  | False = absurd $ contradict (nodeEqReverse $ elemEq p) (sym nil)
deleteMinHelper min (x :: (x' :: xs')) p with (min == x) proof cons
  | True  = x' :: xs'
  | False = x :: deleteMinHelper min (x' :: xs') (elemRes p (nodeNeq (sym cons)))

{- deleteMin wrapper -}
deleteMin : (q : PriorityQueue gsize (S len) weight) ->
            PriorityQueue gsize len weight
deleteMin q@(MKQueue ops (S len) nodes dist)
  = MKQueue ops len (deleteMinHelper (getMin q) nodes (minElem nodes ops dist)) dist



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


--   end of version 3


{-  version2: PriorityQueue with nodes in type

{- remove min from priority queue-}
deleteMinHelper : (min : Node gsize) ->
                  (nodes : Vect (S len) (Node gsize)) ->
                  (p : Elem min nodes) ->
                  Vect len (Node gsize)
deleteMinHelper min (x :: Nil) p with (min == x) proof nil
  | True = Nil
  | False = absurd $ contradict (nodeEqReverse $ elemEq p) (sym nil)
deleteMinHelper min (x :: (x' :: xs')) p with (min == x) proof cons
  | True  = x' :: xs'
  | False = x :: deleteMinHelper min (x' :: xs') (elemRes p (nodeNeq (sym cons)))


deleteMin : (min : Node gsize) ->
            (nodes : Vect (S len) (Node gsize)) ->
            (q : PriorityQueue gsize nodes weight) ->
            (p : Elem min nodes) ->
            (newns : Vect len (Node gsize) ** PriorityQueue gsize newns weight)
deleteMin min nodes (MKQueue ops (S len) nodes dist) p = (newns ** (MKQueue ops len newns dist))
  where
    newns : Vect len (Node gsize)
    newns = deleteMinHelper min nodes p


minQElem (MKQueue _ (S Z) (x :: Nil) dist) = Here
minQElem (MKQueue ops (S (S len)) (x :: (y :: xs)) dist)
  with (dgte ops  (index (getVal x) dist)
                  (index (getVal (getMin $ MKQueue ops (S len) (y :: xs) dist)) dist)) proof minGTx
    | True = There $ minQElem (MKQueue ops (S len) (y :: xs) dist)
    | False = Here



{- proof of  `getMin` -}
getMinCons : (q : PriorityQueue gsize nodes weight) ->
             (min : Node gsize) ->
             (x : Node gsize) ->
             {ops : WeightOps weight} ->
             {p : Elem x' nodes} ->
             (dgte ops (getDist q x) (getDist q min)) = True ->
             (dgte ops (getDist q x') (getDist q min)) = True ->
             {p' : Elem y (x :: nodes)} ->
             dgte ops (getDist q y) (getDist q min) = True

getMinIsMin : (q : PriorityQueue gsize nodes weight) ->
              {p : Elem x nodes} ->
              {ops : WeightOps weight} ->
              (dgte ops (getDist q x) (getDist q (getMin q))) = True
getMinIsMin (MKQueue ops (S Z) (x :: Nil) dist) = ?base --rewrite (elemEq p) in Refl
getMinIsMin (MKQueue ops (S (S len)) (x :: (y :: xs)) dist)
 with (dgte ops (index (getVal x) dist) -- x
                (index (getVal $ getMin (MKQueue ops (S len) (y :: xs) dist)) dist)) proof minX -- min
    | True = ?gmt -- rewrite (getMinIsMin (MKQueue ops (S len) (y :: xs) dist)) in ?refl
    | False = ?gmf --rewrite (get
-}



{-
{- version 1 for getMin v1 with helper -}
{-
{- getMin version1 with helper -}
{- get the node with min distance value within the priorityqueue -}
getMinHelper : (nodes : Vect len (Node gsize) ** PriorityQueue gsize nodes weight)  ->
               (cur : Node gsize) ->
               Node gsize
getMinHelper (Nil ** (MKQueue _ Z Nil _)) cur = cur
getMinHelper ((x :: xs) ** (MKQueue ops (S len) _ dist)) cur {weight}
  = case (dgte ops curd xd) of
         True => getMinHelper (xs ** (MKQueue ops len _ dist)) x
         False => getMinHelper (xs ** (MKQueue ops len _ dist)) cur
  where
    xd : Distance weight
    xd = index (getVal x) dist
    curd : Distance weight
    curd = index (getVal cur) dist

{- get min node from queue -}
getMin : {nodes : Vect (S len) (Node gsize)} ->
         (q : PriorityQueue gsize nodes weight) ->
         Node gsize
getMin {nodes=x :: xs} (MKQueue ops (S len) (x :: xs) dist)
  = getMinHelper (xs ** (MKQueue ops len xs dist)) x
-}



minQElem : (q : PriorityQueue gsize nodes weight) ->
           Elem (getMin q) nodes
minQElem (MKQueue ops (S Z) (x :: Nil) dist) = Here
minQElem (MKQueue ops (S (S len)) (x :: (x' :: xs)) dist)
  with (dgte ops (index (getVal x) dist) (index (getVal x') dist)) proof xdgtex'
    | True = There $ minQElem (MKQueue ops (S len) (x' :: xs) dist)
    | False = elem_insert_mid $ minQElem (MKQueue ops (S len) (x :: xs) dist)
  -}

{- proof of (getMin q) is the min element-}

{- not same distane value, not the same node-}
{-
nodeDisRefl : (d : Node gsize) ->
              (q : PriorityQueue gsize nodes weight) ->
              dgte ops (getDist q d) (getDist q d) = True
nodeDisRefl d q {ops} with (dgte ops (getDist q d) (getDist q d)) proof eq
  | True = Refl
  | False = ?fff

-}

{- need to specify at least one of them is not DInf? -}
{-
getMinIsMin : (q : PriorityQueue gsize nodes weight) ->
              (p : Elem x nodes) ->
              dgte ops (getDist q x) (getDist q (getMin q)) = True
--getMinIsMin q@(MKQueue ops (S Z) (x :: Nil) dist) p = rewrite (elemEq p) in dgteRefl
getMinIsMin (MKQueue ops (S len) (x :: xs) dist) p
  with (dgte ops (getDist (MKQueue ops (S len) (x :: xs) dist) x)
                 (getDist (MKQueue ops (S len) (x :: xs) dist) $ getMin (MKQueue ops (S len) (x :: xs) dist))) proof x_min
    | True = ?gmt --rewrite (getMinIsMin (MKQueue ops len xs dist) ?pp) in ?refl
    | False = ?gmf --rewrite (getMinIsMin (MKQueue ops len xs dist) ?pp) in Refl
  -}




{- examples -}
{- example of PQ with nodes in type
ns : Vect 3 (Node 3)
ns = (n0 :: n1 :: n2 :: Nil)


pq : PriorityQueue 3 PriorityQueue.ns Nat
pq = MKQueue natOps 3 ns (DInf :: DInf :: DInf :: Nil)


ns2 : Vect 2 (Node 3)
ns2 = (n1 :: n2 :: Nil)

pq2 : PriorityQueue 3 PriorityQueue.ns2 Nat
pq2 = MKQueue natOps 2 ns2 (DInf :: DInf :: DInf :: Nil)
-}


{-
n : Node 3
n = getMin $ updateNodeDist pq n2 (DVal 0)
-}
{-
n : Node 3
n with (isQElem n2 pq) proof neElem
  | Yes e = getMin (updateNodeDist pq n2 (DVal 0) {p=e})
  | No ne = void $ (ne $ There (There Here))

-}
{-
 -- this version of priorityqueue always keeps the list of nodes sorted
data PriorityQueue : (len : Nat) -> (gsize : Nat) -> Type -> Type where
  MKQueue : (ops : WeightOps weight) ->
            (len : Nat) ->
            (nodes : Vect len (Node gsize)) ->
            (dist : Vect gsize (Distance weight)) ->
            PriorityQueue len gsize weight


get_min : PriorityQueue (S len) nval weight -> Node nval
get_min (MKQueue _ _ (x :: xs) _) = x


delete_min : PriorityQueue (S len) nval weight ->
             PriorityQueue len nval weight
delete_min (MKQueue ops (S len) (x :: xs) dist) = MKQueue ops len xs dist


cons_elem : PriorityQueue len nval weight ->
            (elem : Node nval) ->
            PriorityQueue (S len) nval weight
cons_elem (MKQueue ops Z Nil dist) e = MKQueue ops (S Z) (e :: Nil) dist
cons_elem (MKQueue ops (S len) xs dist) e = MKQueue ops (S (S len)) (e :: xs) dist


insert_elem : (PriorityQueue len nval weight) ->
              (elem : Node nval) ->
              (PriorityQueue (S len) nval weight)
insert_elem (MKQueue ops Z Nil dist) e = MKQueue ops (S Z) (e :: Nil) dist
insert_elem (MKQueue ops (S len) q@(x@(MKNode xv) :: xs) dist) e@(MKNode ev)
  = case (dgte ops (index ev dist) (index xv dist)) of
         True => cons_elem (insert_elem (MKQueue ops len xs dist) e) x
         False => MKQueue ops (S (S len)) (e :: q) dist


sort_queue : {len : Nat} ->
             (queue : PriorityQueue len nval weight) ->
             (PriorityQueue len nval weight)
sort_queue {len = Z} q = q
sort_queue {len = (S len')} (MKQueue ops (S len') (x :: xs) dist)
  = insert_elem (sort_queue {len = len'} (MKQueue ops len' xs dist)) x
-}

{-
remove_elem : (PriorityQueue (S len) nval weight) ->
              (elem : Node nval) ->
              PriorityQueue len nval weight
remove_elem (MKQueue ops (S len) (x :: xs) dist) e
  = case (x == e) of
         True => MKQueue ops len xs dist
         False => ?l --cons_elem (remove_elem (MKQueue ops len xs dist) e) x
-}

{-
update_elem : {len : Nat} ->
              (PriorityQueue len nval weight) ->
              (n : Node nval) ->
              (new_d : Distance weight) ->
              PriorityQueue len nval weight
update_elem {len = Z} q@(MKQueue _ Z Nil _) _ _ = q
update_elem (MKQueue ops (S len) nodes dist) (MKNode nv) new_d
  = sort_queue {len = S len} (MKQueue ops (S len) nodes (updateAt nv (\x => new_d) dist))
-}





{- useless version for now-}
-- (X) adding a property that the queue is indeed sorted
{-
data PriorityQueue : (gsize : Nat) -> (nodes : Vect len (Node gsize)) -> Type -> Type where
  QNil : PriorityQueue gsize Nil weight
  QCons : (n : Node gsize) ->
          (q : PriorityQueue gsize nodes weight) ->
          (PriorityQueue gsize (n :: nodes) weight)


isQElem : (queue : PriorityQueue gsize nodes weight) ->
          (e : Node gsize) ->
          (Dec (Elem e nodes))
isQElem _ e {nodes} = isElem e nodes


find_min : (queue : PriorityQueue gsize nodes weight) ->
           (cur : Node gsize) ->
           (Elem nodes cur) ->

{- not helpful
 find the index of the node with min distance -}
                           find_min : () ->
           (cur : Node gsize) ->
           (res : Vect len (Node gsize)) ->





delete_node : (nodes : PriorityQueue (S len) gsize weight) ->
              (index : Fin (S len)) ->
              (PriorityQueue len gsize weight)
delete_node (MKQueue ops (S len) nodes dist) index = MKQueue ops len (deleteAt index nodes) dist


get_min : PriorityQueue (S len) gsize weight -> Node gsize
get_min q@(MKQueue ops (S len) nodes@((MKNode xv) :: xs) dist)
  = index (find_min q FZ xs ops dist) nodes
-}
