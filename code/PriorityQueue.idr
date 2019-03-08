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
  
  
{-
remove_elem : (PriorityQueue (S len) nval weight) -> 
              (elem : Node nval) -> 
              PriorityQueue len nval weight
remove_elem (MKQueue ops (S len) (x :: xs) dist) e
  = case (x == e) of 
         True => MKQueue ops len xs dist
         False => ?l --cons_elem (remove_elem (MKQueue ops len xs dist) e) x
-}


update_elem : {len : Nat} -> 
              (PriorityQueue len nval weight) -> 
              (n : Node nval) -> 
              (new_d : Distance weight) -> 
              PriorityQueue len nval weight
update_elem {len = Z} q@(MKQueue _ Z Nil _) _ _ = q
update_elem (MKQueue ops (S len) nodes dist) (MKNode nv) new_d 
  = sort_queue {len = S len} (MKQueue ops (S len) nodes (updateAt nv (\x => new_d) dist)) 
