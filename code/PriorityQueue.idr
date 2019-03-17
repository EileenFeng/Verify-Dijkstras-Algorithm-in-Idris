module PriorityQueue
import Graph
import Data.Vect

%default total
%access public export

{- 
  PriorityQueue of nodes from a given graph (key : node, value : Distance weight)
  sorted in ascending order of distance value
-}

{-
  `dist` holds the distance value for all nodes in the graph regardless of the number of nodes in the queue
-}
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

  {- This version of PQ does not keep the list of nodes sorted, but search for the minimum value during each iteration -} 
  
data PriorityQueue : (gsize : Nat) -> (Vect len (Node gsize)) -> Type -> Type where
  MKQueue : (ops : WeightOps weight) -> 
            (len : Nat) -> 
            (nodes : Vect len (Node gsize)) -> 
            (dist : Vect gsize (Distance weight)) -> 
            PriorityQueue gsize nodes weight


{- check if a node is in priorityqueue -}
isQElem : (target : Node gsize) -> 
          (q : PriorityQueue gsize nodes weight) -> 
          Dec (Elem target nodes)
isQElem n (MKQueue _ _ nodes _) = isElem n nodes


{- get the distance of a specific node -}
getDist : (q : PriorityQueue gsize nodes weight) -> 
          (n : Node gsize) -> 
          {p : isQElem n q = Yes e} ->
          Distance weight
getDist (MKQueue _ _ _ dist) (MKNode nv) = index nv dist
          

{- update the distance of a target node -}
updateDist : (q : PriorityQueue gsize nodes weight) -> 
             (target : Node gsize) -> 
             {p : isQElem target q = Yes e} -> 
             (newd : Distance weight) -> 
             PriorityQueue gsize nodes weight
updateDist (MKQueue ops len nodes dist) (MKNode tv) newd 
  = MKQueue ops len nodes $ updateAt tv (\x => newd) dist


{- get the node with min distance value within the priorityqueue -}
getMinHelper : (nodes : Vect len (Node gsize) ** PriorityQueue gsize nodes weight)  -> 
               (cur : Node gsize) ->  
               Node gsize
getMinHelper (Nil ** (MKQueue _ Z Nil _)) cur = cur
getMinHelper ((x :: xs) ** (MKQueue ops (S len) _ dist)) cur {weight}
  = case (dgt ops curd xd) of
         True => getMinHelper (xs ** (MKQueue ops len _ dist)) x
         False => getMinHelper (xs ** (MKQueue ops len _ dist)) cur
  where
    xd : Distance weight
    xd = index (getVal x) dist
    curd : Distance weight
    curd = index (getVal cur) dist     
  

getMin : {nodes : Vect (S len) (Node gsize)} -> 
         (q : PriorityQueue gsize nodes weight) -> 
         Node gsize
getMin {nodes=x :: xs} q@(MKQueue ops (S len) (x :: xs) dist) 
  = getMinHelper ((x :: xs) ** q) x
  

{- examples -}

ns : Vect 3 (Node 3)
ns = (n0 :: n1 :: n2 :: Nil)         

pq : PriorityQueue 3 PriorityQueue.ns Nat
pq = MKQueue natOps 3 ns (DInf :: DInf :: DInf :: Nil)


ns2 : Vect 2 (Node 3)
ns2 = (n1 :: n2 :: Nil)         

pq2 : PriorityQueue 3 PriorityQueue.ns2 Nat
pq2 = MKQueue natOps 2 ns2 (DInf :: DInf :: DInf :: Nil)


n : Node 3
n with (isQElem n2 pq) proof neElem
  | Yes e = getMin (updateDist pq n2 (DVal 0) {p=Refl})
  | No ne = void $ (ne $ There (There Here))
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
  = case (dgt ops (index ev dist) (index xv dist)) of 
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
