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

data Column : Nat -> (Graph gsize weight ops) -> (Node gsize) -> Type where
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


nodeDistL : {g : Graph gsize weight ops} -> 
            (v : Node gsize) -> 
            (cl : Column len g src) -> 
            Distance weight
nodeDistL (MKNode nv) cl = looseIndexN (finToNat nv) (cdist cl) DInf



nodeDist : {g : Graph gsize weight ops} ->
           (v : Node gsize) ->
           (cl : Column len g src) ->
           Distance weight
nodeDist v cl = index (getVal v) (cdist cl)
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
deleteMinNode x (x :: Nil) Here = Nil
deleteMinNode min (x :: Nil) (There e) = absurd $ noEmptyElem e
deleteMinNode x (x :: (x' :: xs)) Here = (x' :: xs)
deleteMinNode min (x :: (x' :: xs)) (There e) = x :: (deleteMinNode min (x' :: xs) e)
                {-}
deleteMinNode min (x :: Nil) p with (min == x) proof nil
  | True = Nil
  | False = absurd $ contradict (nodeEqReverse $ elemEq p) (sym nil)
deleteMinNode min (x :: (x' :: xs')) p with (min == x) proof cons
  | True  = x' :: xs'
  | False = x :: deleteMinNode min (x' :: xs') (elemRes p (nodeNeq (sym cons)))
-}

deleteMin : {g : Graph gsize weight ops} ->
            (cl : Column (S len) g src) ->
            Column len g src
deleteMin cl@(MKColumn g src (S len) unexp dist)
  = MKColumn g src len (deleteMinNode (getMin cl) unexp (minCElem cl)) dist







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
