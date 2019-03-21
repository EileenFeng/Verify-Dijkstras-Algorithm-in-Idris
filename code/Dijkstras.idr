module Dijkstras

import Graph
import PriorityQueue
import Data.Vect
import Prelude.Basics
import Prelude.List


%default total 

{-
  should the size of `all_nodes` relates to the size of `explored` and `unexplored`? if do, then sort_nodes might have problems as the size of  `targets` is not tightly relates to the size of `all_nodes`
-}

{-
  data structures:
  0. node and weight : use Nat to represent node, and graph is indexed with the Nat of each node
  1. source node
  2. graph : edge value between each adjacent nodes 
  3. distance: distance between each node to source, initially all infinity except source itself
  3. known min value: a set of nodes whose min distance to source is known
  4. 
-}

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



{- proof of minusRefl -}
minusRefl : minus a a = Z
minusRefl {a=Z} = Refl
minusRefl {a=S a'} = minusRefl {a=a'}



{-proof of plusSuccRight-}
plusSuccRight : (a : Nat) -> (b : Nat) -> S (plus a b) = plus a (S b)
plusSuccRight Z Z = Refl
plusSuccRight Z (S b) = Refl
plusSuccRight (S a) b = cong $ plusSuccRight a b



{- converting nat to Fin without maybe -}
natTofin : (m : Nat) -> (n : Nat) -> {auto p : LT m n} -> Fin n
natTofin Z (S n) = FZ
natTofin (S m) (S n) {p = LTESucc _} = FS $ natTofin m n



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
            
                  

{- helper for making list of initial distance values-}
{- 
  {-reverse order, generate list, unable to ensure length-}
mkdist : (gsize : Nat) -> 
         (cur : Nat) -> 
         (p : LTE cur gsize) -> 
         (s : Node gsize) -> 
         (ops : WeightOps weight) -> 
         List (Distance weight)
mkdist Z Z _ _ _ = Nil 
mkdist Z (S _) p _ _ = absurd p
mkdist (S g) Z _ _ _ = Nil
mkdist (S g) (S c) p s@(MKNode f) ops 
  = case (S (finToNat f) == S c) of 
         True => (DVal $ zero ops) :: mkdist (S g) c (lteSuccLeft p) s ops
         False => DInf :: mkdist (S g) c (lteSuccLeft p) s ops
-} 


mkdists : (gsize : Nat) -> 
          (cur : Nat) -> 
          (p : LTE cur gsize) -> 
          (src : Node gsize) -> 
          (ops : WeightOps weight) -> 
          (Vect (minus gsize cur) (Distance weight)) -> 
          (Vect gsize (Distance weight))
mkdists Z Z p _ _ _ = Nil
mkdists Z (S c) p _ _ _ = absurd p
mkdists (S g) Z p _ _ vec = vec
mkdists (S g) (S c) p s@(MKNode sv) ops vec
  = mkdists (S g) c (lteSuccLeft p) s ops $ rewrite (sym $ minusSuccLeft g c (fromLteSucc p)) in ((dv c s ops) :: vec)
    where 
      dv : (cur : Nat) -> (src : Node gsize) -> WeightOps weight -> Distance weight
      dv cur src ops = case (finToNat sv) == cur of 
                        True  => DVal $ zero ops
                        False => DInf
      
    
             


{-
-- need to take in priority queue
-- helper function recur on the list of adj_nodes
update_dist : (weight : Type) -> 
              (gsize : Nat) -> 
              (cur_dist : Distance weight) -> 
              (adj_len : Nat) -> 
              (adj : NodeSet gsize adj_len weight) -> 
              (ql : Nat) -> 
              (old_q : PriorityQueue ql gsize weight) -> 
              (PriorityQueue ql gsize weight) 
update_dist _ _ _ Z (MKSet _ Z _ Nil) _ q = q
update_dist w gsize cur_d (S a) (MKSet w (S a) gsize ((MKNode xv, edge_w) :: xs)) ql q@(MKQueue ops ql _ dist)
  = case (dgt ops (dplus ops cur_d edge_w) (Data.Vect.index xv dist)) of 
         True => update_dist w gsize cur_d a (MKSet w a gsize xs) ql q
         False => update_dist w gsize cur_d a (MKSet w a gsize xs) ql $ update_elem q (MKNode xv) (dplus ops cur_d edge_w)
{-              
update_dist _ _ _ _ (MKSet _ Z _ Nil) dist = dist
update_dist w ops gsize cur_d (MKSet w (S len') gsize ((MKNode xv, edge_w) :: xs)) dist
  = case (dgt (dplus cur_d edge_w) (Data.Vect.index xv dist)) of 
         True => 
         False => 
-}


run_dijkstras : (weight : Type) -> 
                (gsize : Nat) -> 
                (qsize : Nat) -> 
                (lte psize gsize = True) -> 
                (graph : Graph gsize weight) -> 
                (queue : PriorityQueue qsize gsize weight) -> 
                (Vect gsize (Distance weight))
run_dijkstras _ _ Z _ _ (MKQueue _ Z Nil dist) = dist
run_dijkstras w gsize (S qsize') refl g@(MKGraph gsize w edges) q@(MKQueue ops (S qsize') (x@(MKNode xv) :: xs) dist)
  = run_dijkstras w gsize qsize' refl g 
      $ update_dist w gsize (Data.Vect.index xv dist) len adj qsize' (MKQueue ops qsize' xs dist)
      where
        adj =  Data.Vect.index xv edges
        len = length adj
--run_dijkstras w ops gsize (S vsize') refl g@(MKGraph size w edges) ((MKNode xv) :: xs) dist 
  --= run_dijkstras w ops gsize vsize' (lte_succ_refl refl) g xs $ update_dist w ops gsize 
    -- where 
      --  adj = Data.Vect.index xv edges
-}

min : (m : Distance weight) -> 
      (n : Distance weight) -> 
      (ops : WeightOps weight) -> 
      Distance weight
min m n ops = case (dgte ops m n) of 
                   True  => n
                   False => m


updateDist : (cur : Node gsize) -> 
             (neighbors : List (Node gsize, weight)) -> 
             (q : PriorityQueue gsize len weight) -> 
             PriorityQueue gsize len weight
updateDist cur Nil q = q
updateDist cur@(MKNode cv) ((n, w) :: ns) q@(MKQueue ops len nodes dist) {weight}
  = updateDist cur ns $ updateNodeDist q n (min (getNodeDist q n) newD ops)
    where 
      newD : Distance weight 
      newD = dplus ops (index cv dist) (DVal w)
  

runDijkstras : (g : Graph gsize weight) -> 
               (q : PriorityQueue gsize len weight) -> 
               (Vect gsize (Distance weight))
runDijkstras {len=Z} _ (MKQueue ops Z Nil dist) = dist
runDijkstras g@(MKGraph gsize weight edges) q@(MKQueue ops (S len) (x :: xs) dist)
  = runDijkstras g (updateDist min neighbors $ deleteMin q)
  where 
      min : Node gsize 
      min = getMin q
      neighbors : List (Node gsize, weight)
      neighbors = index (getVal min) edges


dijkstras : (gsize : Nat) -> 
            (weight : Type) -> 
            (source : Node gsize) -> 
            (ops : WeightOps weight) -> 
            (graph : Graph gsize weight) -> 
            (Vect gsize (Distance weight))
dijkstras gsize weight src ops g@(MKGraph gsize weight edges) 
  = runDijkstras g (MKQueue ops gsize unexplored dist)
  where 
    unexplored : Vect gsize (Node gsize)
    unexplored = mknodes gsize gsize lteRefl (rewrite (minusRefl {a=gsize}) in Nil)
    
    dist : Vect gsize (Distance weight) 
    dist = mkdists gsize gsize lteRefl src ops (rewrite (minusRefl {a=gsize}) in Nil)
    
    


{- lemmas -}
{- the prefix of a shortest path is also a shortest path-}
prefixSP : (shortest_path g sp {ops}) -> 
           (pathPrefix pre sp) -> 
           (shortest_path g pre)




    
{-
zero : a

infinity : a
--infinity = 999999    

lte_refl : (a : Nat) -> (lte a a = True)
lte_refl Z = Refl
lte_refl (S n) = lte_refl n

lte_succ_refl : (lte (S a) b = True) -> 
                (lte a b = True) 
lte_succ_refl {a=Z} {b=Z} refl = absurd $ trueNotFalse (sym refl)
lte_succ_refl {a=Z} {b=S b'} refl = refl
lte_succ_refl {a=S _} {b=Z} refl = absurd $ trueNotFalse (sym refl)
lte_succ_refl {a=S a'} {b=S b'} refl = lte_succ_refl {a=a'} {b=b'} refl


-- currently weight type is Nat

-- define sorted graph property : nodes are strictly in ascneding ordered accorfing to their distance value 
-- prove that adjusting 

insert_node : (weight : Type) -> 
              (gt_w : weight -> weight -> Bool) -> 
              (add : weight -> weight -> weight) -> 
              (len : Nat) -> 
              (elem : Node m) -> 
              (dist : Vect m weight) -> 
              (nodes : Vect len (Node m)) -> 
              (Vect (S len) (Node m))
insert_node _ _ _ Z e _ Nil = e :: Nil
insert_node w gt_w add (S s') e@(MKNode e_val) dist n@(x@(MKNode x_val) :: xs) 
  = case (gt_w (index e_val dist) (index x_val dist)) of 
         True => x :: (insert_node w gt_w add s' e dist xs)
         False => e :: n


sort_nodes : (weight : Type) -> 
             (gt_w : weight -> weight -> Bool) -> 
             (add : weight -> weight -> weight) -> 
             (size : Nat) -> 
             (nodes : Vect size (Node m)) -> 
             (dist : Vect m weight) -> 
             (Vect size (Node m))
sort_nodes _ _ _ Z Nil _ = Nil 
sort_nodes w gt_w add (S size') (x :: xs) dist 
  = insert_node w gt_w add size' x dist $ sort_nodes w gt_w add size' xs dist


{-
the type of 'nodes' will run into problems during recursion

insert_node : (size : Nat) -> 
              (elem : Node (S size)) -> 
              (dist : Vect (S size) Nat) -> 
              (nodes : Vect size (Node (S size))) -> 
              (Vect (S size) (Node (S size)))
insert_node Z e _ Nil = e :: Nil
sinsert_node (S s') e@(MKNode e_val) dist n@(x@(MKNode x_val) :: xs) 
  = case (gt (index e_val dist) (index x_val dist)) of 
         True => x :: (insert_node s' e (deleteAt x_val dist) xs)
         False => e :: n
             
       
sort_nodes : (size : Nat) -> 
             (nodes : Vect size (Node size)) -> 
             (dist : Vect size Nat) -> 
             (Vect size (Node size))
sort_nodes Z Nil _ = Nil 
sort_nodes (S size') (x :: xs) dist = insert_node size' x dist $ sort_nodes size' (deleteAt x dist)        
-}

-- weird type checking error in idris: recorded in `update_dist` dijkstras_copy.idr: issue at https://github.com/idris-lang/Idris-dev/issues/4313#event-1450393341

-- num and ord

update_dist : (weight : Type) -> 
              (gt_w : weight -> weight -> Bool) -> 
              (add : weight -> weight -> weight) -> 
              (size : Nat) -> 
              (srcVal : Fin size) ->
              (adj : NodeSet size weight) -> 
              (dist : Vect size weight) -> 
              (Vect size weight)
update_dist _ _ _ _ _ (MKSet _ _ Z Nil) dist = dist
update_dist _ gt_w add _ src (MKSet _ _ (S k) ((MKNode n, edge_w) :: xs)) dist 
  = case (gt_w (add (Data.Vect.index src dist) edge_w) (Data.Vect.index n dist)) of
         True => update_dist _ gt_w add _ src (MKSet _ _ k xs) dist
         False => update_dist _ gt_w add _ src (MKSet _ _ k xs) (replaceAt n (add (Data.Vect.index src dist) edge_w) dist)


run_dijkstras : (weight : Type) -> 
                (gt_w : weight -> weight -> Bool) -> 
                (add : weight -> weight -> weight) -> 
                (size : Nat) -> 
                (size' : Nat) -> 
                (lte size' size = True) -> 
                (graph : Graph size weight) -> 
                (dist : Vect size weight) -> 
                (unexplored : Vect size' (Node size)) -> 
                (Vect size weight) 
run_dijkstras _ _ _ _ Z _ _ dist Nil = dist
run_dijkstras w gt_w add s (S s') refl g@(MKGraph s w _ edges) dist ((MKNode x) :: xs) 
  = run_dijkstras w gt_w add s s' (lte_succ_refl refl) g
                  (update_dist w gt_w add s x (Data.Vect.index x edges) dist)
                  (sort_nodes w gt_w add s' xs $ update_dist w gt_w add s x (Data.Vect.index x edges) dist)


{- properties of weight-}
dijkstras : (weight : Type) -> 
            (gt_w : weight -> weight -> Bool) -> 
            (add : weight -> weight -> weight) -> 
            (zero : weight) -> 
            (infinity : weight) -> 
            (size : Nat) -> 
            (source : Node size) -> 
            (graph : Graph size weight) -> 
            (Vect size weight) 
dijkstras w gt_w add zero inf size src g@(MKGraph size w nodes edges) 
  = run_dijkstras w gt_w add size size (lte_refl size) g dist unexplored
    where 
      dist = map (\x => if (x == src) then zero else infinity) nodes
      unexplored = sort_nodes w gt_w add size nodes dist
    --new_graph = MKGraph size w (sort_nodes size nodes dist) edges
-}

--graph : Graph 5 Nat

{-
n1 : Node 5
n1 = MKNode FZ

n2 : Node 5
n2 = MKNode 1

n3 : Node 5
n3 = MKNode 2

n4 : Node 5
n4 = MKNode 3

n5 : Node 5
n5 = MKNode 4

n1_set : NodeSet 5 Nat
n1_set = MKSet Nat 5 [(n2, 5), (n3, 1)]

n2_set : NodeSet 5 Nat
n2_set = MKSet Nat 5 [(n4, 3)]

n3_set : NodeSet 5 Nat
n3_set = MKSet Nat 5 [(n5, 10)]

n4_set : NodeSet 5 Nat
n4_set = MKSet Nat 5 [(n5, 1)]

n5_set : NodeSet 5 Nat
n5_set = MKSet Nat 5 []

nodes : Vect 5 (Node 5)
nodes = [n1, n2, n3, n4, n5]

graph : Graph 5 Nat
graph = MKGraph 5 Nat [n1, n2, n3, n4, n5] [n1_set, n2_set, n3_set, n4_set, n5_set]


res : Vect 5 Nat 
res = dijkstras Nat gt plus Z 989 5 n1 graph
-}
{-
 _____________VERSION 2____________

--insert_node : 

update_graph : (source_dist : Nat) -> 
               (adj_nodes : Nodeset Nat) -> 
               (dist : List (Node, Nat)) -> 
               (List (Node, Nat))
update_graph _ (MKSet _ Nil) dist = dist
update_graph src (MKSet _ ((MKNode n, edge_w) :: xs)) dist 
  = case (src + edge_w) < cur_dist of 
         True => update_graph src (MKSet _ xs) $ 
                              map (\c => if (fst c) == (fst x) 
                                         then (fst c, src + egde_w) 
                                         else c) dist
         False => update_graph src (MKSet _ xs) dist
9  where 
    cur_dist = snd $ index n dist
    
    
   


-- currently assume edge weight is Nat
run_dijkstras : (unexplored : List Node) -> 
                (distMap : List (Node, Nat)) ->
                (g : Graph Nat) -> --adjacent nodes 
                (List (Node, Nat))   
run_dijkstras Nil distMap g = distMap
run_dijkstras (x :: xs) dist g@(MKGraph _ _ nodesets) = ?j --run_dijkstras xs $ sort (update distances



{-
dijkstras : (weight : Type) -> 
            (comparator : (w1 : weight) -> (w2 : weight) -> Bool) ->
            (source : Graph.node) -> 
            (g : graph weight) ->  
            (List (node, weight)) -- distance from source to each node
-}


{-
  input graph: 'nodes' in ascending order, 'nodesets' ordered by ascending order of 'nodes'
-}
dijkstras : (source : Node) -> 
            (g : Graph Nat) ->  
            (List (Node, Nat)) -- distance from source to each node
dijkstras s g@(MKGraph _ adjMatrix) = run_dijkstras nodes distances g
  where 
    distances = map (\x => if (fst x) == s then (x, 0) else (x, infinity)) adjMatrix
-- distances has type: ((Node, Nodeset), dist)
  
{-

-}





_____________VERSION 1______________
{-
run_dijkstras : (weight : Type) -> 
                (comparator : (w1 : weight) -> (w2 : weight) -> Bool) ->
                (explored : List Graph.node) -> 
                (unexplored : List Graph.node) -> 
                (distance : List (Graph.node, weight)) ->
                (g : graph weight) -> --adjacent nodes 
                (List (Graph.node, weight))
-}

run_dijkstras : (explored : List Graph.node) -> 
                (unexplored : List Graph.node) -> 
                (distance : List (Graph.node, Nat)) ->
                (g : graph Nat) -> --adjacent nodes 
                (List (Graph.node, Nat))   
run_dijkstras exp Nil distance g = distance
run_dijkstras exp (x :: xs) distance g = ?h


{-
dijkstras : (weight : Type) -> 
            (comparator : (w1 : weight) -> (w2 : weight) -> Bool) ->
            (source : Graph.node) -> 
            (g : graph weight) ->  
            (List (node, weight)) -- distance from source to each node
-}

dijkstras : (source : Graph.node) -> 
            (g : graph Nat) ->  
            (List (Graph.node, Nat)) -- distance from source to each node
dijkstras s g = run_dijkstras Nil unexp distances g
  where 
    unexp = map Prelude.Basics.fst g
    distances = map (\x => if (Prelude.Basics.fst x == s) then (Prelude.Basics.fst x, 0) else (Prelude.Basics.fst x, infinity)) g


sort_nodes : (weight : Type) -> 
             (comparator : (w1 : weight) -> (w2 : weight) -> Bool) ->
             (targets : List Nat) -> 
             (g : graph weight) -> 
             (List Nat) -- sorted list of node index 
-}
{-
  1. sort unexplored ascending 
  2. get the first inlist
  3. updated 
-}
  
                 


