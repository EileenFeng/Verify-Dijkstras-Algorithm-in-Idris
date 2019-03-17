module Graph
import Data.Vect

%access public export 
%default total

contradict : p = True -> 
             p = False -> 
             Void
contradict Refl Refl impossible


{- Nat triangle inequality-}
lte_plusZ : lte a (plus a Z) = True
lte_plusZ {a=Z} = Refl
lte_plusZ {a=S a'} = lte_plusZ {a=a'}


nat_tri : (a : Nat) -> (b : Nat) -> gte (plus a b) a = True
nat_tri Z Z = Refl
nat_tri a Z with (gte (plus a Z) a) proof lte_a_z
  | True = Refl
  | False = absurd $ contradict (lte_plusZ {a=a}) (sym lte_a_z)
nat_tri Z b with (gte (plus Z b) Z) proof gte_z_b
  | True = Refl
  | False = absurd $ trueNotFalse (sym gte_z_b)
nat_tri (S a) (S b) 
  = nat_tri a (S b)

 
{- `distance` and `weight` types -} 
using (weight : type) 
  record WeightOps weight where 
    constructor MKWeight
    zero : weight
    gtew : weight -> weight -> Bool
    gteRefl : {a : weight} -> (gtew a a = True)
    eq : weight -> weight -> Bool
    add : weight -> weight -> weight
    triangle_ineq : (a : weight) -> (b : weight) -> gtew (add a b) a = True
    add_comm : (a : weight) -> (b : weight) -> add a b = add b a


-- any value added to infinity should be infinity
-- need to define arithmetics for Distance type
data Distance : Type -> Type where
  DInf : Distance weight
  DVal : (val : weight) -> Distance weight


-- plus for Distance type
dplus : (ops : WeightOps weight) -> 
        (Distance weight) -> 
        (Distance weight) -> 
        (Distance weight) 
dplus _ DInf _ = DInf
dplus _ _ DInf = DInf 
dplus ops (DVal v1) (DVal v2) = DVal $ (add ops) v1 v2

-- greater than or equal to for Distance type
dgt : (ops : WeightOps weight) -> 
      Distance weight -> 
      Distance weight -> Bool
dgt _ _ DInf = False
dgt _ DInf _ = True
dgt ops (DVal v1) (DVal v2) = (gtew ops) v1 v2


dgtRefl : dgt ops d d = True
dgtRefl {d = DInf} = ?dinf
dgtRefl {d= DVal dv} {ops} with (gtew ops dv dv) proof dvRefl
  | True = Refl
  | False = absurd $ contradict (gteRefl ops) (sym dvRefl)
  

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
  
   
getVal : Node gsize -> Fin gsize
getVal (MKNode v) = v


{- equality for Fin-}
finEq : (f1, f2 : Fin n) -> 
        (f1 == f2) = True -> 
        f1 = f2
finEq FZ FZ refl = Refl
finEq (FS f1) FZ Refl impossible
finEq FZ (FS f2) Refl impossible
finEq (FS f1) (FS f2) refl = cong $ finEq f1 f2 refl


finEqReverse : {f1, f2 : Fin n} -> 
               f1 = f2 -> 
               (f1 == f2) = True
finEqReverse {f1=FZ} {f2=FZ} refl = Refl
finEqReverse {f1=FS _} {f2=FZ} Refl impossible
finEqReverse {f1=FZ} {f2=FS _} Refl impossible
finEqReverse {f1=FS f1'} {f2=FS f2'} refl = finEqReverse {f1=f1'} {f2=f2'} (FSInjective f1' f2' refl)


finNeqSucc : {f1, f2 : Fin n} -> 
             Not (f1 = f2) -> 
             Not (FS f1 = FS f2)
finNeqSucc {f1} {f2} refl e = absurd $ refl (FSinjective e)



finNeq : {f1, f2 : Fin n} -> 
         (f1 == f2) = False -> 
         Not (f1 = f2)
finNeq {f1=FZ} {f2=FZ} refl e = absurd $ trueNotFalse refl
finNeq {f1=FS f1'} {f2=FZ} refl Refl impossible
finNeq {f1=FZ} {f2=FS f2'} refl Refl impossible
finNeq {f1=FS f1'} {f2=FS f2'} refl e = finNeqSucc (finNeq {f1=f1'} {f2=f2'} refl) e



{- equality for nodes -}
nodeEq : (a, b : Node gsize) -> 
         (a == b) = True -> 
         (a = b)
nodeEq (MKNode av) (MKNode bv) refl = cong $ finEq av bv refl

{- a = b -> a == b = True -}
nodeEqReverse : {a, b : Node gsize} ->  
                (a = b) -> 
                (a == b) = True
nodeEqReverse {a=MKNode av} {b=MKNode bv} refl with (av == bv) proof eq 
  | True = Refl
  | False = absurd $ contradict (finEqReverse $ NodeInjective {f1=av} {f2=bv} refl) (sym eq)
  
  
nodeNeq : {a, b : Node gsize} -> 
          (a == b) = False -> 
          Not (a = b)
nodeNeq {a=MKNode av} {b=MKNode bv} refl e = finNeq refl (NodeInjective e)--finNeq av bv refl


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
get_neighbors : (g : Graph gsize weight) -> 
                (n : Node gsize) -> 
                (nodeset gsize weight)
get_neighbors (MKGraph _ _ edges) (MKNode nv) = index nv edges


{- there is an edge from node 'n' to node 'm' -}
adj : {g : Graph gsize weight} -> 
      (n, m : Node gsize) -> Type
adj {g} n m = (inNodeset m (get_neighbors g n) = True)



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
              (adj {g=g} n m) -> 
              weight
edge_weight g n m adj = get_weight (get_neighbors g n) m adj

{-
  {- path with distance -} 
data Path : Node gsize -> 
            Node gsize -> 
            (weight : Type)  -> 
            Graph gsize weight -> 
            Distance weight -> Type where
  Unit : (g : Graph gsize weight) -> 
         (n : Node gsize) ->
         (ops : WeightOps weight) ->
         Path n n weight g (DVal $ zero ops) 
  Cons : Path s v weight g d -> 
         (n : Node gsize) -> 
         (adj : adj {g=g} v n) ->
         (ops : WeightOps weight) ->  
         Path s n weight g (dplus ops d (DVal $ edge_weight g v n adj))


shortestPath : (sp : Path s v w g d) -> 
               (lp : Path s v w g ld) -> 
               {ops : WeightOps w} -> 
               Type 
shortestPath {d} {ld} sp lp {ops} = (dgt ops ld d = True)


-}


  {- path without distance in Type -}

data Path : Node gsize -> 
            Node gsize -> 
            (weight : Type) -> 
            Graph gsize weight -> Type where
  Unit : (g : Graph gsize weight) -> 
         (n : Node gsize) -> 
         Path n n weight g
  Cons : Path s v weight g-> 
            (g : Graph gsize weight) -> 
            (n : Node gsize) -> 
            (adj : adj {g=g} v n) ->
            Path s n weight g


{- length of path -}
length : Path s v weight g -> 
         WeightOps weight -> 
         Distance weight
length (Unit _ _) ops = DVal $ zero ops
length (Cons (Unit _ s) g v adj) ops = DVal $ edge_weight g s v adj
length (Cons (Cons p _ s _) g v adj) ops 
  = dplus ops (DVal $ edge_weight g s v adj) (length p ops)

{- shortest path -}
-- `sp` stands for shortest path, `lp` stands for any other path
-- this definition seems inaccurate as `lp` refers to a specific s-v path rather than any s-v path in g
shortest_path : (sp : Path s v w g) ->
                (lp : Path s v w g) -> 
                (ops : WeightOps w) -> 
                Type 

                





-- example with Nat as weight
n0 : Node 3
n0 = MKNode FZ

n1 : Node 3
n1 = MKNode (FS FZ)

n2 : Node 3
n2 = MKNode (FS (FS FZ))

set0 : nodeset 3 Nat 
set0 = [(n2, 4)]

set1 : nodeset 3 Nat
set1 = [(n0, 4), (n2, 6)]

set2 : nodeset 3 Nat
set2 = Nil

g : Graph 3 Nat
g = MKGraph 3 Nat (set0 :: set1 :: set2 :: Nil)

gteRefl : gte a a = True
gteRefl {a=Z} = Refl
gteRefl {a=S a'} = gteRefl {a=a'}

natOps : WeightOps Nat
natOps = MKWeight Z gte gteRefl (==) plus nat_tri plusCommutative

{-
p1 : Path Graph.n1 Graph.n1 Nat Graph.g (DVal Z)
p1 = Unit g n1 natOps

p12 : Path Graph.n1 Graph.n2 Nat Graph.g (DVal 6)
p12 = Cons p1 n2 Refl natOps
-}




--p3 : Path Graph.n1 Graph.n2 Nat ?d
--p3 = Cons (Cons p1 g n0 Refl natOps) g n2 Refl natOps



{-
*Graph> adj {g=g} n1 n0
True = True : Type
*Graph> adj {g=g} n2 n0
False = True : Type
*Graph> edge_weight g n1 n0 Refl
4 : Nat
-}



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

