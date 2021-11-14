module Dijkstras

import Graph
import Column
import Data.Vect
import Data.Vect.Quantifiers
import Prelude.Basics
import Prelude.List


-- %default total
%access public export

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

{-
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
-}



{- get the min from two numbers -}
min : (ops : WeightOps weight) ->
      (m : Distance weight) ->
      (n : Distance weight) ->
      Distance weight
min ops m n = case (dgte ops m n) of
                   True  => n
                   False => m


minRefl : {ops : WeightOps weight} ->
          {m : Distance weight} ->
          min ops m (dplus ops m DInf) = m
minRefl {m=DInf} = Refl
minRefl {m=DVal w} = Refl

{-}
calcDist : (g : Graph gsize weight ops) ->
           (dist : Vect gsize (Distance weight)) ->
           (minN : Node gsize) ->
           (cur : Node gsize) ->
           Distance weight
calcDist g dist minN cur {ops}
  with (inNodeset cur (getNeighbors g minN)) proof adj
    | True = min (index (getVal cur) dist)
                 (dplus ops (index (getVal minN) dist) (DVal (edge_weight $ sym adj))) ops
    | False = index (getVal cur) dist

updateDist1 : (g : Graph gsize weight ops) ->
              (minN : Node gsize) ->
              (cur : Nat) ->
              {auto p : LTE (S cur) gsize} ->
              (old : Vect gsize (Distance weight)) ->
              (new : Vect gsize (Distance weight)) ->
              Vect gsize (Distance weight)
updateDist1 g minN Z old new = replaceAt FZ (calcDist g old minN x) new
updateDist1 g minN (S len) old new
  = updateDist1 g minN len old $ replaceAt (natTofin len gsize) (calcDist g old minN (MKNode)) new
-}

calcDist : (g : Graph gsize weight ops) ->
            (minN : Node gsize) ->
            (cur : Node gsize) ->
            (old : Vect gsize (Distance weight)) ->
            Distance weight
calcDist g minN cur old {ops}
  = min ops (index (getVal cur) old)
              (dplus ops (index (getVal minN) old) (edgeW g minN cur))


{-
calcDist : (g : Graph gsize weight ops) ->
           (minN : Node gsize) ->
           (cur : Node gsize) ->
           (old : Vect gsize (Distance weight)) ->
           Distance weight
calcDist g minN cur old {ops}
  = case (inNodeset cur (getNeighbors g minN)) of
      True => min ops (index (getVal cur) old)
                          (dplus ops (index (getVal minN) old) (DVal $ ?e))
      False => index (getVal cur) old
-}

total
updateDistR : {gsize : Nat} ->
              {weight : Type} ->
              {ops : WeightOps weight} ->
              {n : Nat} ->
              {auto p : LTE n gsize} ->
              (g : Graph gsize weight ops) ->
              (cur : Node gsize) ->
              (distance_to_cur : Distance weight) ->
              (dist : Vect n (Distance weight)) ->
              Vect n (Distance weight)
updateDistR g cur distance_to_cur Nil = Nil
updateDistR {n=S n'} g cur distance_to_cur (x::xs) {ops} {gsize} {p}
  = Dijkstras.min ops x (dplus ops distance_to_cur (edgeW g cur (MKNode (natTofin n' gsize)))) ::
    updateDistR g cur distance_to_cur xs {p=lteSuccLeft p}

updateDist : (g : Graph gsize weight ops) ->
              (cur : Node gsize) ->
              (nodes : Vect m (Node gsize)) ->
              {auto p : LTE m gsize} ->
              (dist : Vect gsize (Distance weight)) ->
              Vect gsize (Distance weight)
updateDist g cur Nil dist = dist
updateDist g cur (x :: xs) dist {p}
  = updateDist g cur xs (replaceAt (getVal x) (calcDist g cur x dist) dist) {p=lteSuccLeft p}
{-
updateDist0 g cur (x :: xs) old new {p} with (inNodeset x (getNeighbors g cur)) proof adj
  | True = updateDist0 g cur xs old
              (replaceAt (getVal x)
                (min ops (index (getVal x) old)
                  (dplus ops (index (getVal cur) old) (DVal $ edge_weight (sym adj))))
                  new) {p=lteSuccLeft p}
  | False = updateDist0 g cur xs old (replaceAt (getVal x) (index (getVal x) old) new) {p=lteSuccLeft p}
-}

{-
updateDist : (cur : Node gsize) ->
             (neighbors : nodeset gsize weight) ->
             (ops : WeightOps weight) ->
             (olddist : Vect gsize (Distance weight)) ->
             (newdist : Vect gsize (Distance weight)) ->
             Vect gsize (Distance weight)
updateDist _ Nil _ _ newdist = newdist
updateDist cur ((n, w) :: xs) ops olddist newdist {weight} {gsize}
 = updateDist cur xs ops olddist (replaceAt (getVal n) newD newdist)
 where
   d' : Distance weight
   d' = dplus ops (index (getVal cur) olddist) (DVal w)
   newD : Distance weight
   newD = min ops d' (index (getVal n) olddist)

-}

updateDistR2 : (g : Graph gsize weight ops) ->
               (dist : Vect gsize (Distance weight)) ->
               (min_node : Node gsize) ->
               Vect gsize (Distance weight)
updateDistR2 g dist min_node {ops} {gsize} {weight} = zipWith (min ops) dist new_dists
  where
  min_dist : Distance weight
  min_dist = index (getVal min_node) dist

  new_dists : Vect gsize (Distance weight)
  new_dists = map (dplus ops min_dist) $
              map (edgeW g min_node) $
              mkNodes gsize


updateDistProperty : (g : Graph gsize weight ops) ->
                     (min_node : Node gsize) ->
                     (dist : Vect gsize (Distance weight)) ->
                     Vect gsize (Distance weight) ->
                     Type
updateDistProperty g min_node dist new_dist {gsize}
  = (n : Node gsize) ->
    (inNodeset n (getNeighbors g min_node) = False) ->
    dEq ops (index (getVal n) dist) (index (getVal n) new_dist) = True
    {-
    All (\n => inNodeset n ... = False -> dEq ops ... = True) new_dist

-}
zipWithProof : {fun : b -> c -> a} ->
               (xs : Vect n b) ->
               (ys : Vect n c) ->
               (prop : a -> Type) ->
               (pf1 : All (prop . uncurry fun) (zip xs ys)) ->
               All prop (zipWith fun xs ys)
zipWithProof (x :: xs) (y :: ys) prop (pf :: pfs)
  = pf :: zipWithProof xs ys prop pfs

updateEqR2 : (g : Graph gsize weight ops) ->
             (min_node : Node gsize) ->
             (dist : Vect gsize (Distance weight)) ->
             updateDistProperty g min_node dist (updateDistR2 g dist min_node)
updateEqR2 g min_node dist = ?rae


runHelper : {g : Graph gsize weight ops} ->
            (cl : Column (S len) g src) ->
            Column len g src
runHelper cl@(MKColumn g src (S len) unexp dist) {gsize} {weight} {ops}
  = MKColumn g src len (deleteMinNode min unexp (minCElem cl)) newds
  where
    min : Node gsize
    min = getMin cl
    newds : Vect gsize (Distance weight)
    newds = updateDistR g min (Data.Vect.index (getVal min) dist) dist {p=lteRefl}
    --newds = updateDist g min (mkNodes gsize) dist {p=lteRefl}
    --newds = updateDist min (getNeighbors g min) ops dist dist


runDijkstras : {g : Graph gsize weight ops} ->
               (cl : Column len g src) ->
               Column Z g src
runDijkstras {len = Z} {src} cl = cl
runDijkstras {len = S l'} cl@(MKColumn g src (S l') _ _ ) = runDijkstras $ runHelper cl



dijkstras : (gsize : Nat) ->
            (g : Graph gsize weight ops) ->
            (src : Node gsize) ->
            (Vect gsize (Distance weight))
dijkstras Z g s = absurd $ NodeZAbsurd s
dijkstras gsize g@(MKGraph gsize weight ops edges) src
  = cdist $ runDijkstras (MKColumn g src gsize nodes dist)
  where
    nodes : Vect gsize (Node gsize)
    nodes = mkNodes gsize
    dist : Vect gsize (Distance weight)
    dist = mkdists gsize src ops



-- helper proofs of Dijkstras
{- `updateEq` and `udEq` are helper proofs for `naDistEq`,
as `runHelper` is defined with `updateDist` and `calcDist`.  -}

udEq : (g : Graph gsize weight ops) ->
       (m, c : Node gsize) ->
       (old : Vect gsize (Distance weight)) ->
       (na : Not (adj g m c)) ->
       dEq ops (index (getVal c) old) (calcDist g m c old) = True
udEq g m c old na {ops} with (edgeW g m c) proof isAdj
  | (DVal w) = ?lllt--absurd $ na (edgeW_adj {w=w} (sym isAdj))
  | DInf with (dgte ops (index (getVal c) old) (dplus ops (index (getVal m) old) DInf)) proof dgt
      | True = ?fff
      | False = dEqRefl


updateEq : (g : Graph gsize weight ops) ->
           (mn : Node gsize) ->
           (nodes : Vect m (Node gsize)) ->
           (dist : Vect gsize (Distance weight)) ->
           (e : Elem c nodes) ->
           (na : Not (adj g mn c)) ->
           {auto p : LTE m gsize} ->
           dEq ops (index (getVal c) dist) (index (getVal c) (updateDist g mn nodes dist)) = True
updateEq g mn Nil _ e _ = absurd $ noEmptyElem e
updateEq g mn (v :: Nil) old Here na = ?d

looseIndex : Fin n -> Vect m a -> a -> a
looseIndex _ Nil deflt = deflt
looseIndex FZ (x :: _) _ = x
looseIndex (FS n') (_ :: xs) deflt = looseIndex n' xs deflt

helperHelper : (gsize : Nat) ->
               (weight : Type) ->
               (ops : WeightOps weight) ->
               (g : Graph gsize weight ops) ->
               (n' : Nat) ->
               (p : LTE (S n') gsize) ->
               (cur : Node gsize) ->
               (v : Node gsize) ->
               (distance_to_cur : Distance weight) ->
               (x : Distance weight) ->
               (xs : Vect n' (Distance weight)) ->
               Not (adj g cur v) ->
               (inn : Bool) ->
               (inNodeset (MKNode (natTofin n' gsize)) (getNeighbors g cur)) = inn ->
               dEq ops (looseIndex (getVal v) (x::xs) DInf)
                       (looseIndex (getVal v) (updateDistR {gsize=gsize} {n=S n'} g cur distance_to_cur (x::xs)) DInf) = True
helperHelper gsize weight ops g n' p cur v distance_to_cur x xs pf_not True pf_inn = ?rae1
helperHelper gsize weight ops g n' p cur v distance_to_cur x xs pf_not False pf_inn = ?rae2

naDistEqHelper : (gsize : Nat) ->
                 (weight : Type) ->
                 (ops : WeightOps weight) ->
                 (g : Graph gsize weight ops) ->
                 (n : Nat) ->
                 (p : LTE n gsize) ->
                 (cur : Node gsize) ->
                 (v : Node gsize) ->
                 (distance_to_cur : Distance weight) ->
                 (dist : Vect n (Distance weight)) ->
                 Not (adj g cur v) ->
                 dEq ops (looseIndex (getVal v) dist DInf)
                         (looseIndex (getVal v) (updateDistR {gsize=gsize} {n=n} g cur distance_to_cur dist) DInf) = True
naDistEqHelper _ _ _ _ _ _ _ _ _ Nil _ = Refl
naDistEqHelper gsize weight ops g (S n') p cur v distance_to_cur (x::xs) pf_not
  = helperHelper gsize weight ops g n' p cur v distance_to_cur x xs pf_not
                 (inNodeset (MKNode (natTofin n' gsize)) (getNeighbors g cur)) Refl
{-
with (inNodeset {gsize=gsize} {weight=weight} (MKNode (natTofin ?rae3 gsize {p=?rae5})) (getNeighbors g cur)) -- (inNodeset (MKNode (natTofin n' gsize)) (getNeighbors g cur)) proof isAdj
 | True = ?rae1
 | False = ?rae2
-}
naDistEq : {g : Graph gsize weight ops} ->
           (cl : Column (S len) g src) ->
           (v : Node gsize) ->
           (ne: Not (adj g (getMin cl) v)) ->
           dEq ops (index (getVal v) (cdist cl)) (index (getVal v) (cdist $ runHelper cl)) = True
naDistEq {g} cl@(MKColumn g src (S len) nodes dist) v ne -- with (inNodeset v (getNeighbors g (getMin cl))) proof isAdj
  = ?ef



{- ============================= LEMMAS ============================== -}

{-----------------------------------------------------------------------
  [Lemma 3.1]: the prefix of a shortest path is also a shortest path
------------------------------------------------------------------------}

{- lemma 3.1 helper: (length p1) < length(p2) -> length(p1+p3) < length(p1+p3)-}
shorter_trans : {g : Graph gsize weight ops} ->
                (p1 : Path s w g) ->
                (p2 : Path s w g) ->
                (p3 : Path w v g) ->
                (p : dgte ops (length p1) (length p2) = False) ->
                dgte ops (length $ append p1 p3) (length $ append p2 p3) = False
shorter_trans p1 p2 (Unit _ _) prf = prf
shorter_trans p1 p2 (Cons p3' v adj) prf
  = dgteBothPlus (edge_weight adj) $ shorter_trans p1 p2 p3' prf

{- lemma 3.1 proof -}
l1_prefixSP : {g: Graph gsize weight ops} ->
              (shortestPath g sp) ->
              (pathPrefix sp_pre sp) ->
              (shortestPath g sp_pre)
l1_prefixSP spath (post ** appendRefl) lp_pre {ops} {sp_pre}
  with (dgte ops (length lp_pre) (length sp_pre)) proof lpsp
    | True = Refl
    | False = absurd $ contradict (spath (append lp_pre post))
                                         (rewrite (sym appendRefl)
                                                  in (shorter_trans lp_pre sp_pre post (sym lpsp)))


{--------------------------------------------------------------------------------
  Lemma2: if dist[v]_{n+1} != infinity, then there is a s-v path
---------------------------------------------------------------------------------}
-- statement
neDInfPath : {g : Graph gsize weight ops} ->
             (cl : Column len g src) ->
             Type
neDInfPath cl {src} {ops} {gsize} {g}
  = (v : Node gsize) ->
    (ne : dEq ops DInf (nodeDist v cl) = False) ->
    (psw : Path src v g ** dEq ops (length psw) (nodeDist v cl) = True)


sameDist : (psw ** (dEq ops (length psw) d1 = True)) ->
           (dEq ops d1 d2 = True) ->
           (psw ** (dEq ops (length psw) d2 = True))
sameDist (p ** e) e12 = ?sd

l2_existPath : {g : Graph gsize weight ops} ->
               (cl : Column (S len) g src) ->
               (ih : neDInfPath cl) ->
               neDInfPath (runHelper cl)
l2_existPath {g} cl ih v ne {ops} with (inNodeset v (getNeighbors g (getMin cl))) proof isAdj
  | True = ?lt
  | False = ?lf --sameDist (ih v (dEqTransTF ne (neDInfNotAdj cl v (sym isAdj)))) (dEqComm (neDInfNotAdj cl v (sym isAdj)))


{-
neDInfTrans : {g : Graph gsize weight ops} ->
(cl : Column (S len) g src) ->
(v : Node gsize) ->
(ne : dEq ops DInf (index (getVal v) (cdist cl)) = False) ->
dEq ops DInf (index (getVal v) (cdist $ runHelper cl)) = False
neDInfTrans cl v ne = ?kk

l2_trans : {g : Graph gsize weight ops} ->
(cl : Column (S len) g src) ->
(v : Node gsize) ->
(ne : dEq ops DInf (index (getVal v) (cdist cl)) = False) ->
(psv : Path src v g ** dEq ops (length psv) (index (getVal v) (cdist cl)) = True) ->
(dEq ops DInf (index (getVal v) (cdist (runHelper cl))) = False) ->
(psv' : Path src v g ** dEq ops (length psv') (index (getVal v) (cdist (runHelper cl))) = True)
l2_trans cl v prop {ne} = ?l2t
-}


{-----------------------------------------------------------------------------------------------------
 Lemma 3 : forall v \in g, dist_{i+1}[v] = \delta(v) ->
           \forall j > i, dist_{j+1}[v] = \delta(v)
------------------------------------------------------------------------------------------------------}
-- stm : dist[v] = \delta(v)
distIsDelta : {g : Graph gsize weight ops} ->
              (cl : Column len g src) ->
              Type
distIsDelta cl {g} {gsize} {ops} {src}
  = (v : Node gsize) ->
    (psv : Path src v g) ->
    (sp : shortestPath g psv) ->
    dEq ops (nodeDist v cl) (length psv) = True


l3_preserveDelta : {g : Graph gsize weight ops} ->
                   (cl : Column (S len) g src) ->
                   (ih : distIsDelta cl) ->
                   distIsDelta (runHelper cl)
l3_preserveDelta {g} cl ih v psv sp with (inNodeset v (getNeighbors g (getMin cl))) proof adj
  | True = ?l3t
  | False = dEqComm $ dEqTransTrue (dEqComm $ ih v psv sp) (naDistEq cl v (bnot $ sym adj))





{---------------------------------------------------------------------------------------------
  Lemma 4 : For any node v ∈ g, for each ui ∈ exploredn+1, n ≥ 1, 1 ≤ i ≤ n,
            distn+1[v] ≤ disti[ui] + weight(ui, v).

            but dist_i[u_i] = \delta(u_i)
----------------------------------------------------------------------------------------------}









{------------------------------------------------------------
  Lemma 5 : Forall node v ∈ exploredn+1:
    1. distn+1[v] < ∞
    2. distn+1[v] ≤ δ(v′), ∀v′ ∈ unexploredn+1.
    3. distn+1[v] = δ(v)
--------------------------------------------------------------}
-- statement 1: distn+1[v] < ∞
lessInf : {g : Graph gsize weight ops} ->
          (cl : Column len g src) ->
          Type
lessInf cl {gsize} {ops}
  = (v : Node gsize) ->
    (explored v cl) ->
    dEq ops (nodeDist v cl) DInf = False

-- statement 2: distn+1[v] ≤ δ(v′), ∀v′ ∈ unexploredn+1.
unexpDelta : {g : Graph gsize weight ops} ->
             (cl : Column len g src) ->
             Type
unexpDelta cl {g} {gsize} {ops} {src}
  = (v, v' : Node gsize) ->
    (explored v cl) ->
    (unexplored v' cl) ->
    (psv' : Path src v' g) ->
    (sp : shortestPath g psv') ->
    dgte ops (length psv') (nodeDist v cl) = True

-- statement 3 :  distn+1[v] = δ(v) similar to stm of lemma 3

-- all three statements for lemma 5
l5_stms : {g : Graph gsize weight ops} ->
          (cl : Column len g src) ->
          Type
l5_stms cl = (lessInf cl, unexpDelta cl, distIsDelta cl)


l5_sp : (l5_stms cl) -> distIsDelta cl
l5_sp (s1, s2, s3) = s3

l5_spath : {g : Graph gsize weight ops} ->
           (cl : Column (S len) g src) ->
           (ih : l5_stms cl) ->
           l5_stms (runHelper cl)
{- l5_spath {len=Z} (MKColumn g src (S Z) (x :: Nil) dist) (ih1, ih2, ih3)
  = (?l6, ?l7, ?l8) -}

{- proof of correctness -}
correctness : {g : Graph gsize weight ops} ->
              (cl : Column len g src) ->
              (stms : l5_stms cl) ->
              l5_stms (runDijkstras cl)
correctness {len = Z} cl stms = stms
correctness {len=S n} cl@(MKColumn g src (S n) _ _) stms
  = correctness (runHelper {len=n} cl) (l5_spath cl stms)


dijkstras_correctness : (gsize : Nat) ->
                        (g : Graph gsize weight ops) ->
                        (src : Node gsize) ->
                        (v : Node gsize) ->
                        (psv : Path s v g) ->
                        (spsv : shortestPath g psv) ->
                        dEq ops (length psv) (index (getVal v) (dijkstras gsize g src)) = True
dijkstras_correctness Z g src _ _ _ = absurd $ NodeZAbsurd src
dijkstras_correctness gsize g src v psv spsv {weight} {ops}
  = ?dk --(l5_sp $ correctness cl ?stms) v psv spsv
  where
    nodes : Vect gsize (Node gsize)
    nodes = mknodes gsize gsize lteRefl (rewrite (minusRefl {a=gsize}) in Nil)
    dist : Vect gsize (Distance weight)
    dist = mkdists gsize src ops


{-
correctness : {g : Graph gsize weight ops} ->
              (cl : Column gsize g src) ->
              (v : Node gsize) ->
              (psv : Path s v g) ->
              (spsv : shortestPath g psv) ->
              dEq ops (length psv) (nodeDist v (runDijkstras cl)) = True
correctness {gsize=Z} _ v _ _ = absurd $ NodeZAbsurd v
-- base case here
correctness {gsize =(S (S gs))} cl v psv spsv
  -}

{-correctness {gsize = S len} cl v psv spsv
  = apply lemma 5 to (correctness {gsize = len} cl' v psv spsv)-}


{-===========================================================

-- dijkstra's version one

updateDist0 : (cur : Node gsize) ->
             (neighbors : List (Node gsize, weight)) ->
             (q : PriorityQueue gsize len weight) ->
             PriorityQueue gsize len weight
updateDist0 cur Nil q = q
updateDist0 cur@(MKNode cv) ((n, w) :: ns) q@(MKQueue ops len nodes dist) {weight}
  = updateDist0 cur ns $ updateNodeDist q n (min (getNodeDist n q) newD ops)
    where
      newD : Distance weight
      newD = dplus ops (index cv dist) (DVal w)


runDijkstras0 : (g : Graph gsize weight) ->
               (q : PriorityQueue gsize len weight) ->
               (Vect gsize (Distance weight))
runDijkstras0 {len=Z} _ (MKQueue ops Z Nil dist) = dist
runDijkstras0 g@(MKGraph gsize weight edges) q@(MKQueue ops (S len) (x :: xs) dist)
  = runDijkstras0 g (updateDist0 min neighbors $ deleteMin q)
  where
      min : Node gsize
      min = getMin q
      neighbors : List (Node gsize, weight)
      neighbors = getNeighbors g min



dijkstras : (gsize : Nat) ->
            (weight : Type) ->
            (source : Node gsize) ->
            (ops : WeightOps weight) ->
            (graph : Graph gsize weight) ->
            (Vect gsize (Distance weight))
dijkstras gsize weight src ops g@(MKGraph gsize weight edges)
  = runDijkstras0 g (MKQueue ops gsize unexplored dist)
  where
    unexplored : Vect gsize (Node gsize)
    unexplored = mknodes gsize gsize lteRefl (rewrite (minusRefl {a=gsize}) in Nil)

    dist : Vect gsize (Distance weight)
    dist = mkdists gsize gsize lteRefl src ops (rewrite (minusRefl {a=gsize}) in Nil)


-}

{-
{--------------------------------------------------------------------------------
  Lemma2: if dist[v]_{n+1} != infinity, then there is a s-v path
---------------------------------------------------------------------------------}
l2_existPath : (g : Graph gsize weight) ->
               (s : Node gsize) ->
               (q : PriorityQueue gsize (S len) weight) ->
               (prop : (dEq (qops q) DInf (getNodeDist w q) = False) ->
               (psw : Path s w g ** (dEq (qops q) (length (qops q) psw) (getNodeDist w q)) = True)) ->
               (ne : dEq (qops q) DInf (index (getVal v) (runDijkstras g q)) = False) ->
               (psv : Path s v g ** (dEq (qops q) (length (qops q) psv) (index (getVal v) (runDijkstras g q))) = True)




{-----------------------------------------------------------------------------------------------------
  Lemma 3 : forall v \in g, dist_{i+1}[v] = \delta(v) ->
            \forall j > i, dist_{j+1}[v] = \delta(v)
------------------------------------------------------------------------------------------------------}

l3_preserveDelta : (g : Graph gsize weight) ->
                   (q: PriorityQueue gsize (S len) weight) ->
                   (v : Node gsize) ->
                   (d : (spsv : Path s v g ** shortestPath g spsv (qops q))) ->
                   (eq : (dEq (qops q) (getNodeDist v q) (delta d)) = True) ->
                   dEq (qops q) (index (getVal v) (runDijkstras g q)) (delta d) = True




{---------------------------------------------------------------------------------------------
   Lemma 4 : For any node v ∈ g, for each ui ∈ exploredn+1, n ≥ 1, 1 ≤ i ≤ n,
             distn+1[v] ≤ disti[ui] + weight(ui, v).
----------------------------------------------------------------------------------------------}
l4_minDist : (g : Graph gsize weight) ->
             (q : PriorityQueue gsize len weight) ->
             (epd : explored q v) ->
             (adjp : adj g w v) ->
             dgte (qops q)
                  (dplus (qops q) (getNodeDist w q) (DVal $ edge_weight adjp))
                  (getNodeDist v q) = True





{------------------------------------------------------------
  Lemma 5 : Forall node v ∈ exploredn+1:
    1. distn+1[v] < ∞
    2. distn+1[v] ≤ δ(v′), ∀v′ ∈ unexploredn+1.
    3. distn+1[v] = δ(v)
--------------------------------------------------------------}
{- statement of a node v's distance value is not infinity -}
distNotInf : (q : PriorityQueue gsize len weight) ->
             (v : Node gsize) ->
             (exq : explored q v) ->
             Type
distNotInf q v exp = dgte (qops q) DInf (getNodeDist v q) = True

{- statement: v \in explored and v' \in unexplored, distance of v smaller than delta(v')-}
distSDelta : {g : Graph gsize weight} ->
             (q : PriorityQueue gsize len weight) ->
             (w, v : Node gsize) ->
             (explored q v) ->
             (QElem w q) ->
             (pw : Path s w g ** shortestPath g pw (qops q)) ->
             Type
distSDelta q w v exp_v unexp_w dp = dgte (qops q) (delta dp) (getNodeDist v q) = True


{- statement that a node v's distance value equals delta(v) -}
eqDelta : {g : Graph gsize weight} ->
          (q : PriorityQueue gsize len weight) ->
          (pv : Path s v g ** shortestPath g pv (qops q)) ->
          Type
eqDelta q pv {v} = dEq (qops q) (delta pv) (getNodeDist v q) = True


l5_stms : (g : Graph gsize weight) ->
          (q : PriorityQueue gsize len weight) ->
          (s : Node gsize) ->
          (unexp : QElem w q) ->
          (exp : explored q v) ->
          --(dpw : (pw : Path s w g ** shortestPath g pw (qops q))) ->
          --(dpv : (pv : Path s v g ** shortestPath g pv (qops q))) ->
          Type
l5_stms g q s unexp exp {w} {v}
  =  (dpw : (pw : Path s w g ** shortestPath g pw (qops q))) ->
     (dpv : (pv : Path s v g ** shortestPath g pv (qops q))) ->
     (distNotInf q v exp) ->
     (distSDelta q w v exp unexp dpw) ->
     (eqDelta q dpv)


l5_shortestDist : (g : Graph gsize weight) ->
                  (q : PriorityQueue gsize len weight) ->
                  (s : Node gsize) ->
                  (unexp : QElem w q) ->
                  (exp : explored q v) ->
                  (ih : l5_stms g q s unexp exp) ->
                  (unexp' : QElem w' (updateQDist q (runDijkstras g q))) ->
                  (exp' : explored (updateQDist q (runDijkstras g q)) v') ->
                  l5_stms g (updateQDist q (runDijkstras g q)) s unexp' exp'
l5_shortestDist {gsize = Z} _ _ s _ _ _ _ _ = absurd $ NodeZAbsurd s
l5_shortestDist {gsize = S Z} g q s unexp exp ih unexp' exp' = ?l51

{- proof of dijktra's -}
graph_oneNode : (g : Graph (S Z) weight) ->
                (v, w : Node (S Z)) ->
                v = w


dijkstras_base : (g : Graph (S Z) weight) ->
                 (ops : WeightOps weight) ->
                 (s : Node (S Z)) ->
                 (v : Node (S Z)) ->
                 dEq ops (index (getVal v) (dijkstras (S Z) weight s ops g))
                          (DVal $ zero ops) = True


dijkstras_correctness : (gsize : Nat) ->
                        (g : Graph gsize weight) ->
                        (s : Node gsize) ->
                        (v : Node gsize) ->
                        (ops : WeightOps weight) ->
                        (pv : Path s v g ** shortestPath g pv ops) ->
                        dEq ops (index (getVal v) (dijkstras gsize weight s ops g)) (length ops pv) = True
dijkstras_correctness Z _ s _ _ _ = absurd $ NodeZAbsurd s
dijkstras_correctness gsize@(S len) g s v ops pv = ?ll--l5_shortestDist g (MKQueue


--dijkstras_correctness (S Z) g s v ops pv = ?d1
-}



{- lemma2 trials
existPath : (v : Node gsize) ->
            (s : Node gsize) ->
            (g : Graph gsize weight) ->
            {q : PriorityQueue gsize len weight} ->
            (ne : dEq (qops q) DInf (getNodeDist v $ updateDist cur (getNeighbors g cur) q) = False) ->
            (p : Path s v g ** (dEq (qops q)
                                      (length (qops q) p)
                                      (getNodeDist v $ updateDist cur (getNeighbors g cur) q)) = True)
-}
{-
existPath : {gsize : Nat} ->
            {s : Node gsize} ->
            {ops : WeightOps weight} ->
            (v : Node gsize) ->
            (ne : dEq ops DInf (index (getVal v) (dijkstras gsize weight s ops g)) = False) ->
            (p : Path s v g ** (dEq ops (length ops p)
                                        (index (getVal v) (dijkstras gsize weight s ops g))) = True)
existPath {gsize = Z} v ne = absurd $ NodeZAbsurd v
existPath {gsize = S Z} {weight} {ops} {s} {g} v ne = ?base
{-
  with (runDijkstras g (MKQueue ops (S Z)
                     (mknodes gsize gsize lteRefl (rewrite (minusRefl {a=gsize}) in Nil))-}

existPath {gsize = S len} v ne = ?is
-}


{- version before priorityqueue -}
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
