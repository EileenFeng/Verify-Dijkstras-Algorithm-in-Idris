module Dijkstras

import Graph
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
         True => update_dist _ gt_w add _ src (MKSet _ _ k xs) (replaceAt n (add (Data.Vect.index src dist) edge_w) dist)
         False => update_dist _ gt_w add _ src (MKSet _ _ k xs) dist


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
                  (sort_nodes w gt_w add s' xs dist)



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
  
                 


