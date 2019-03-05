                             module Graph
import Data.Vect

%access public export 
%default total
{-
  over break:
  0. implementing(pseudocode)/proof dijkstra's in paper (latex): pseudocode based on idris, termination proof on paper
  1. implementing dijkstra's in idris
  2. paper proof: keep track of lemmas (assumptions) 
 
  1. [(node, [(adj_node, weight_para)])] (maybe use set instead of list: https://github.com/jfdm/idris-containers/blob/master/Data/AVL/Set.idr, set: substraction)
    - define set as list, sorted, de-duplication (set in other languages (Coq, Agda))
    - lemma on sets independent of what's stored underneath the set structure 
  (backup plan. graph as a function from node to set of adjacent nodes)
-}

-- restrict the size of NodeSet, Graph according to the number of Nodes
 
{- `distance` and `weight` types -} 


-- implement WeightOps as Record 
-- wraps all operations for a given weight type
using (weight : type) 
  record WeightOps weight where 
    constructor MKWeight
    gtw : weight -> weight -> Bool
    add : weight -> weight -> weight
    triangle_ineq : (a : weight) -> (b : weight) -> gtw (add a b) a = True
    add_comm : (a : weight) -> (b : weight) -> add a b = add b a


-- any value added to infinity should be infinity
-- need to define arithmetics for Distance type
data Distance : Type -> Type where
  DZero : Distance weight
  DInf : Distance weight
  DVal : (val : weight) -> Distance weight


-- plus for Distance type
dplus : (ops : WeightOps weight) -> 
        (Distance weight) -> 
        (Distance weight) -> 
        (Distance weight) 
dplus _ dval DZero = dval
dplus _ DZero dval = dval
dplus _ DInf _ = DInf
dplus _ _ DInf = DInf 
dplus ops (DVal v1) (DVal v2) = DVal $ (add ops) v1 v2

-- greater than for Distance type
dgt : (ops : WeightOps weight) -> 
      Distance weight -> 
      Distance weight -> Bool
dgt _ DZero _ = False
dgt _ _ DZero = True
dgt _ _ DInf = False
dgt _ DInf  _ = True
dgt ops (DVal v1) (DVal v2) = (gtw ops) v1 v2


data Node : Nat -> Type where
  MKNode : Fin n -> Node n

NodeInjective : {f1 : Fin n} -> {f2 : Fin n} -> (MKNode f1 = MKNode f2) -> (f1 = f2)
NodeInjective Refl = Refl


implementation Eq (Node n) where 
  (==) (MKNode f1) (MKNode f2) = f1 == f2
  
implementation DecEq (Node n) where 
  decEq (MKNode n1) (MKNode n2) with (decEq n1 n2) 
    | Yes refl = Yes $ cong refl
    | No neq   = No $ \h : MKNode n1 = MKNode n2 => neq $ NodeInjective h
  
  
get_nval : Node gsize -> Fin gsize
get_nval (MKNode v) = v

-- define NodeSet as type synonym(List) : gsize weight
nodeset : (gsize : Nat) -> (weight : Type) -> Type
nodeset gsize weight = List (Node gsize, weight) 


{- return true if 'ns' contains an entry for node 'n', false otherwise-}
inNodeset : (n : Node gsize) -> 
            (ns : nodeset gsize weight) ->
            Bool
inNodeset _ Nil = False
inNodeset n ((x, w) :: xs) 
  = case (x == n) of 
         True => True
         False => inNodeset n xs


{- Properties of inNodeset -}
   

{- unsafe get_weight
{- get weight value for node 'n' in the given nodeset -}
get_weight : (edges : nodeset gsize weight) -> 
             (n : Node gsize) -> 
             weight
get_weight Nil n = ?g
get_weight ((x, w) :: xs) n
  = case (x == n) of 
         True => w
         False => get_weight xs n
-}       

data Graph : Nat -> Type -> Type where
  MKGraph : (gsize : Nat) -> 
            (weight : Type) -> 
            (edges : Vect gsize (nodeset gsize weight)) -> 
            Graph gsize weight


{- if a node value is smaller than graph size, then it is in the graph
gelem : (g : Graph gsize weight) -> (n : Node gsize) -> Type 
gelem (MKGraph _ _ edge) (MKNode nv) = (lte (finToNat nv) gsize = True)
-}



{-give the edges of a certain node 'n' in graph 'g' -}
adj_nodes : (g : Graph gsize weight) -> 
            (n : Node gsize) -> 
            (nodeset gsize weight)
adj_nodes (MKGraph _ _ edges) (MKNode nv) = index nv edges


{- there is an edge from node 'n' to node 'm' -}
adj_n_m : {g : Graph gsize weight} -> 
          (n, m : Node gsize) -> Type
adj_n_m {g} n m = (inNodeset m (adj_nodes g n) = True)



{- get the weight of certain edge adjacent to m, helper of edge_weight-}
get_weight : (ns : nodeset gsize weight) -> 
             (m : Node gsize) -> 
             (inNodeset m ns = True) -> 
             weight
get_weight Nil m inset = absurd $ trueNotFalse (sym inset)
get_weight ((x, w) :: xs) m inset
  with (x == m) proof x_eq_m
   | True = w
   | False = get_weight xs m inset



{- weight of edge from node 'n' to 'm' in graph 'g' -}
edge_weight : (g : Graph gsize weight) -> 
              (n : Node gsize) -> 
              (m : Node gsize) -> 
              (adj_n_m {g=g} n m) -> 
              weight
edge_weight g n m adj = get_weight (adj_nodes g n) m adj







{- old node set 
data NodeSet : (gsize : Nat) -> (ssize : Nat) -> Type -> Type where 
  MKSet : (weight : Type) -> 
          (ssize : Nat) -> 
          (gsize : Nat) -> 
          Vect ssize (Node gsize, weight) -> 
          NodeSet gsize ssize weight


{- existential -}
data Graph : Nat -> Type -> Type where
  MKGraph : (size : Nat) -> 
            (weight : Type) -> 
            (edges : Vect size (len : Nat ** NodeSet size len weight)) -> 
            Graph size weight
-} 



{- old WeightOps data type
data WeightOps : Type -> Type where
  -- needs to make sure that for (a,b : weight) -> 
  MKWeight : (weight : Type) -> 
             (gt_w : weight -> weight -> Bool) -> 
             (add : weight -> weight -> weight) -> 
             (triangle_ineq : (a : weight) -> (b : weight) -> gt_w (add a b) a = True) -> 
             (add_comm : (a : weight) -> (b : weight) -> add a b = add b a) -> 
             WeightOps weight
-}


                        
{-
data Dist : Nat -> Type -> Type where
  MKDist : (size : Nat) -> 
           (weight : a) -> 
           Vect size a -> Dist size a
-}
         
-- _____________ VERSION 2______________
{-
--node : Type
--node = Nat

data Node : Type where 
  MKNode : Nat -> Node
 
Eq Node where 
  (==) (MKNode a) (MKNode b) = a == b
  
Show Node where 
  show (MKNode n) = show n



{-
  `nodeset` is used for representing all the adjacent nodes for a particular node in the graph
-}

data Nodeset : Node -> Type -> Type where
  MKSet : a -> List (Node, a) -> Nodeset a

data Graph : Nat -> Type -> Type where
  MKGraph : (size : Nat) -> Vect size (Node, Nodeset a) -> Graph size a

-}





-- _____________GRAPH VERSION 1______________
{-
nodeset : Type -> Type 
nodeset weight = List (node, weight)

graph : Type -> Type
graph weight = List (node, nodeset weight)
-}

--gmap : Functor f => (a -> b) -> graph a -> graph b
--gmap f (





{-
data Tree : a -> Type where 
  Leaf : a -> Tree a
  Node : (Tree a) -> a -> (Tree a) -> Tree a


data GNode : Type where
  GN : (a : Nat) -> GNode


data Edge : Type where
  MKEdge : (n1 : GNode) -> (n2 : GNode) -> Edge


Eq GNode where
  (GN a) == (GN b) = (a == b)


implementation DecEq GNode where 
  decEq (GN a) (GN b) with (decEq a b)
    | Yes refl = ?de1
    | No notEq = No ?de2


nodeset : Type
nodeset = Tree GNode


nodemap : Type -> Type
nodemap a = Tree a


graph : Type
graph = nodemap nodeset


data TElem : a -> (Tree a)  -> Type where 
  TLeaf : TElem x (Leaf x)
  Root  : TElem x (Node lt x rt)
  Left  : (left : TElem x lt) -> TElem x (Node lt y rt)
  Right : (right : TElem x rt) -> TElem x (Node lt y rt)

{-
data GElem : a -> Graph.graph -> Type where
  GLeaf : GElem (nodemap
-}

isTElem : DecEq a => (x : a) -> (t : Tree a) -> Dec (TElem x t)
{-isTElem x (Leaf n) with (decEq x n) 
  | Yes refl = Yes TLeaf
  | No noteq = No noteq
isTElem x (Node t1 n t2) with (decEq x n) 
  | Yes refl  = Yes Root
  | No notRoot with (isTElem x t1)
    | Yes is_left = Left is_left
    | No not_left = isTElem x t2
-}

getRoot : Tree GNode -> GNode
getRoot (Leaf l) = l
getRoot (Node _ r _) = r


adj : (g : Graph.graph) -> (i : GNode) -> Maybe Graph.nodeset
adj (Leaf t) i = case (getRoot t == i) of
                      True  => Just t
                      False => Nothing
adj (Node t1 node t2) i 
  = case (getRoot node == i) of
         True => Just node
         False => case (adj t1 i) of 
                       Just n => Just n
                       Nothing => adj t2 i


no_selfloop : (i : GNode) -> 
              (g : Graph.graph) -> 
              (TElem i g) ->
              Not (TElem i (adj g i))
-}

