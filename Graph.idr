module Graph

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


{-
  over break:
  0. implementing(pseudocode)/proof dijkstra's in paper (latex): pseudocode based on idris, termination proof on paper
  1. implementing dijkstra's in idriss 
  2. paper proof: keep track of lemmas (assumptions) 
 
  1. [(node, [(adj_node, weight_para)])] (maybe use set instead of list: https://github.com/jfdm/idris-containers/blob/master/Data/AVL/Set.idr, set: substraction)
    - define set as list, sorted, de-duplication (set in other languages (Coq, Agda))
    - lemma on sets independent of what's stored underneath the set structure 
  2. 
-}
