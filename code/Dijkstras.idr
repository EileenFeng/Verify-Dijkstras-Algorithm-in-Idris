module Dijkstras

import Graph
import Column
import Data.Vect
import Data.Vect.Quantifiers
import Prelude.Basics
import Prelude.List


%default total
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


minusInj : minus a b = minus (S a) (S b)


-- LTE proofs
lteMinus : (gsize, n : Nat) ->
           (p : LTE (S n) gsize) ->
           LT (minus gsize (S n)) gsize
lteMinus Z _ LTEZero impossible
lteMinus (S g) Z p = rewrite (minusZ {a=g}) in lteRefl
lteMinus (S g) (S n) (LTESucc p) = lteSuccRight $ lteMinus g n p



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




ndist : (v : Node gsize) ->
        (dist : Vect gsize (Distance weight)) ->
        Distance weight
ndist (MKNode nv) dist = looseIndex nv dist DInf




{- working version 1 hard to prove with recursion -}
calcDistV4 : (g : Graph gsize weight ops) ->
             (min_node : Node gsize) ->
             (cur : Node gsize) ->
             (min_dist : Distance weight) ->
             (cur_dist : Distance weight) ->
             Distance weight
calcDistV4 g min_node cur min_dist cur_dist
  = min ops cur_dist (dplus ops min_dist (edgeW g min_node cur))



updateDist6 :  (g : Graph gsize weight ops) ->
               (min_node : Node gsize) ->
               (min_dist : Distance weight) ->
               (nodes : Vect m (Node gsize)) ->
               (dist : Vect m (Distance weight)) ->
               Vect m (Distance weight)
updateDist6 g min_node min_dist Nil Nil = Nil
updateDist6 g min_node min_dist (x :: xs) (d :: ds)
  = (calcDistV4 g min_node x min_dist d) :: (updateDist6 g min_node min_dist xs ds)



runHelper : {g : Graph gsize weight ops} ->
            (cl : Column (S len) g src) ->
            Column len g src
runHelper cl@(MKColumn g src (S len) unexp dist) {gsize} {weight} {ops}
  = MKColumn g src len (deleteMinNode min_node unexp (minCElem cl)) newds
  where
    min_node : Node gsize
    min_node = getMin cl
    min_dist : Distance weight
    min_dist = index (getVal min_node) dist
    newds : Vect gsize (Distance weight)
    newds = updateDist6 g min_node min_dist (mkNodes gsize) dist




runDijkstras : {g : Graph gsize weight ops} ->
               (cl : Column len g src) ->
               Column Z g src
runDijkstras {len = Z} {src} cl = cl
runDijkstras {len = S l'} cl@(MKColumn g src (S l') _ _ ) = runDijkstras $ runHelper cl



dijkstras : (gsize : Nat) ->
            (g : Graph gsize weight ops) ->
            (src : Node gsize) ->
            (Vect gsize (Distance weight))
--dijkstras Z g s = absurd $ NodeZAbsurd s
dijkstras gsize g src {weight} {ops} = cdist $ runDijkstras cl
  where
    nodes : Vect gsize (Node gsize)
    nodes = mkNodes gsize
    dist : Vect gsize (Distance weight)
    dist = mkdists gsize src ops
    cl : Column gsize g src
    cl = (MKColumn g src gsize nodes dist)




-- helper proofs of Dijkstras
{- proof of calcDistV4 -}
calcDistV4Eq : (g : Graph gsize weight ops) ->
               (min_node : Node gsize) ->
               (cur : Node gsize) ->
               (min_dist : Distance weight) ->
               (cur_dist : Distance weight) ->
               dgte ops cur_dist (calcDistV4 g min_node cur min_dist cur_dist) = True
calcDistV4Eq g min_node cur min_dist cur_dist {ops}
  with (dgte ops cur_dist (dplus ops min_dist (edgeW g min_node cur))) proof sdist
    | True = sym sdist
    | False = dgteRefl



distDecre : (g : Graph gsize weight ops) ->
            (mn : Node gsize) ->
            (min_dist : Distance weight) ->
            (nodes : Vect m (Node gsize)) ->
            (dist : Vect m (Distance weight)) ->
            (nv : Nat) ->
            {auto p : LT nv m} ->
            dgte ops (indexN nv dist) (indexN nv (updateDist6 g mn min_dist nodes dist)) = True
distDecre g mn _ Nil Nil nv {p} = absurd $ succNotLTEzero p
distDecre g mn min_dist (n :: ns) (d :: ds) Z = calcDistV4Eq g mn n min_dist d
distDecre g mn min_dist (n :: ns) (d :: ds) (S nv) {p=LTESucc p'} = distDecre g mn min_dist ns ds nv {p= p'}



runDecre : {g : Graph gsize weight ops} ->
           (cl : Column (S len) g src) ->
           (v : Node gsize) ->
           dgte ops (nodeDistN v cl) (nodeDistN v (runHelper cl)) = True
runDecre (MKColumn g src (S len) unexp dist) (MKNode nv) {gsize} {ops}
  = distDecre g min_node min_dist (mkNodes gsize) dist (finToNat nv) {p=nvLTE nv}
  where
    min_node : Node gsize
    min_node = (getMinNode unexp ops dist)
    min_dist : Distance weight
    min_dist = (index (getVal (getMinNode unexp ops dist)) dist)



{- path to Min -}


{- if `d` is equal to the length of some path, then d < DInf-}
pathlenNotDInf : {g : Graph gsize weight ops} ->
                 {s, v : Node gsize} ->
                 (d : Distance weight) ->
                 (psv : Path s v g) ->
                 (eq : dEq ops d (length psv) = True) ->
                 dgte ops d DInf = False
pathlenNotDInf d (Unit g _) eq {ops} = dgteEqTrans eq False (dgteZeroInf {ops=ops})
pathlenNotDInf d (Cons p' n adj) eq {g} {ops}
  = dgteEqTrans eq False $
                dvalNotInf {ops=ops} {d1=length p'} {w=edge_weight adj} (pathlenNotDInf (length p') p' (dEqRefl {ops=ops} {d=length p'}))




{- if a node `v` is explored in current Column `cl`, then it is also explored in `runHelper cl` -}
expV_preserve : {g : Graph gsize weight ops} ->
                (cl : Column (S len) g src) ->
                (v : Node gsize) ->
                (exp : explored v cl) ->
                explored v (runHelper cl)
expV_preserve cl@(MKColumn g src (S len) unexp dist) v exp ne
  = deleteNElem (getMin cl) v unexp (minCElem cl) exp ne



{-if a node 'v' is explored after  `runHelper cl` and `v` is not (getMin cl), then `v` not in cl -}
expV_VNotMin :  {g : Graph gsize weight ops} ->
                (cl : Column (S len) g src) ->
                (v : Node gsize) ->
                (expVR : explored v (runHelper cl)) ->
                (notMin : Not ((getMin cl) = v)) ->
                explored v cl
expV_VNotMin cl@(MKColumn g src (S len) unexp dist) v expVR notMin expv
  = deleteNElemRev (getMin cl) v unexp (minCElem cl) expVR notMin expv



{- there always exists a node with not infinity distance in unexplored (if not Nil)-}
unexpV_not_DInf : {g : Graph gsize weight ops} ->
                  (cl : Column (S len) g src) ->
                  (src_ninf : dgte ops (nodeDistN src cl) DInf = False) ->
                  dgte ops (nodeDistN (getMin cl) cl) DInf = False


unexpReverse : {g : Graph gsize weight ops} ->
               (cl : Column (S len) g src) ->
               (v : Node gsize) ->
               (ve : unexplored v (runHelper cl)) ->
               unexplored v cl
unexpReverse cl@(MKColumn g src (S len) unexp dist) v ve
  = deleteMinElem (getMin cl) v unexp (minCElem cl) ve


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
              {s, v, w : Node gsize} ->
              {sp : Path s v g} ->
              {sp_pre : Path s w g} ->
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
neDInfPath cl {g} {src} {ops} {gsize}
  = (v : Node gsize) ->
    (ne : dgte ops (nodeDistN v cl) DInf = False) ->
    (psv : Path src v g ** dEq ops (nodeDistN v cl) (length psv) = True)



l2_existPath : {g : Graph gsize weight ops} ->
               (cl : Column (S len) g src) ->
               (ih : neDInfPath cl) ->
               neDInfPath (runHelper cl)
l2_existPath {g} cl ih = ?l2



{-----------------------------------------------------------------------------------------------------
 Lemma 3 : forall v \in g, dist_{i+1}[v] = \delta(v) ->
           \forall j > i, dist_{j+1}[v] = \delta(v)
------------------------------------------------------------------------------------------------------}
-- stm : dist[v] = \delta(v)
{-distIsDelta : {g : Graph gsize weight ops} ->
              (cl : Column len g src) ->
              Type
distIsDelta cl {g} {gsize} {ops} {src}
  = (v : Node gsize) ->
    (psv : Path src v g) ->
    (sp : shortestPath g psv) ->
    dEq ops (nodeDistN v cl) (length psv) = True
-}


-- (ihD v psv psv_sp) gives `dEq ops (nodeDistN v cl) (length psv) = True` ([E1])
-- (pathlenNotDInf (nodeDIstN v cl) psv (ihD v psv psv_sp)) gives `dgte ops (nodeDistN v cl) DInf = False`
-- (runDecre cl v) gives `dgte ops (nodeDistN v cl) (nodeDistN (runHelper cl)) = True` ([R])
-- dgteDInfTrans (nodeDistN v cl) (nodeDistN v (runHelper vl)) (pathlenNotDInf (nodeDistN v cl) psv (ihD v psv psv_sp)) (runDecre cl v))
                 -- gives `dgte ops (nodeDistN v (runHelper cl) DInf = False`, which can be applied Lemma 2 to obtain
                 -- dependent pair `(path_sv ** dEq ops (nodeDistN v (runHelper cl)) (length path_sv) = True)` ([E2])
-- but `psv` is the shortestPath, `spsv path_sv` gives `dgte (length path_sv) (length psv) = True` ([E3]), which is equivalent to
  -- `dgte (nodeDistN v (runHelper cl)) (nodeDistN v cl) = True` ([E4]), combine this with [R], we know ` dEq (nodeDistN v (runHelper cl)) (nodeDistN v cl) = True`
    -- which gives us `dEq (nodeDistN v (runHelper cl)) (length psv) = True`, whic is `distIsDelta (runHelper cl) v psv`
-- l2_existPath cl

l3_preserveDelta : {g : Graph gsize weight ops} ->
                   (cl : Column (S len) g src) ->
                   (l2_ih : neDInfPath cl) ->
                   (v : Node gsize) ->
                   (psv : Path src v g) ->
                   (spsv : shortestPath g psv) ->
                   (eq : dEq ops (nodeDistN v cl) (length psv) = True) ->
                   dEq ops (nodeDistN v (runHelper cl)) (length psv) = True
l3_preserveDelta cl l2_ih v psv psv_sp eq {g} {ops} {src}
  with (l2_existPath cl l2_ih v (dgteDInfTrans {ops=ops} (nodeDistN v cl) (nodeDistN v (runHelper cl)) (pathlenNotDInf (nodeDistN v cl) psv eq) (runDecre cl v)))
    | (lpath ** runclv_lp) = dgteEq (dgteEqTrans runclv_lp True (psv_sp lpath)) (dgteEqTrans (dEqComm eq) True (runDecre cl v))



{-
l3_preserveDelta : {g : Graph gsize weight ops} ->
                   (cl : Column (S len) g src) ->
                   (l2_ih : neDInfPath cl) ->
                   (l3_ih : distIsDelta cl) ->
                   distIsDelta (runHelper cl)
l3_preserveDelta cl l2_ih l3_ih v psv psv_sp {g} {ops} {src}
  with (l2_existPath cl l2_ih v (dgteDInfTrans {ops=ops} (nodeDistN v cl) (nodeDistN v (runHelper cl)) (pathlenNotDInf (nodeDistN v cl) psv (l3_ih v psv psv_sp)) (runDecre cl v)))
    | (lpath ** runclv_lp) = dgteEq (dgteEqTrans runclv_lp True (psv_sp lpath)) (dgteEqTrans (dEqComm $ l3_ih v psv psv_sp) True (runDecre cl v))
-}

{-
{---------------------------------------------------------------------------------------------
  Lemma 4 : For any node v ∈ g, for each ui ∈ exploredn+1, n ≥ 1, 1 ≤ i ≤ n,
            distn+1[v] ≤ disti[ui] + weight(ui, v).

----------------------------------------------------------------------------------------------}
distv_min : {g : Graph gsize weight ops} ->
            (cl : Column len g src) ->
            Type
distv_min cl = (v, ui : Node gsize) ->
               (exp_ui : explored ui cl) ->
               dgte ops (nodeDistN v cl) (dplus ops (nodeDistN ui cl) (edgeW g ui v)) = False

l4_distVIsMin : {g : Graph gsize weight ops} ->
                (cl : Column (S len) g src) ->
                (distv_min cl) ->
                distv_min (runHelper cl)
l4_distVIsMin cl l4_ih v u_i exp_ui
  with (getMin cl == ui) proof min_is_ui
    | True = ?l4t
    | False = ?l4f
-}






{------------------------------------------------------------
  Lemma 5 : Forall node v ∈ exploredn+1:
    1. distn+1[v] < ∞
    2. distn+1[v] ≤ δ(v′), ∀v′ ∈ unexploredn+1.
    3. distn+1[v] = δ(v)
--------------------------------------------------------------}
-- statement 1: distn+1[v] < ∞
lessDInf : {g : Graph gsize weight ops} ->
          (cl : Column len g src) ->
          Type
lessDInf cl {gsize} {ops}
  = (v : Node gsize) ->
    (explored v cl) ->
    dgte ops (nodeDistN v cl) DInf = False

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
    dgte ops (length psv') (nodeDistN v cl) = True


-- statement 3 : For any node v ∈ g, for each w ∈ exploredn+1, n ≥ 1, 1 ≤ i ≤ n, distn+1[v] ≤ distn[w] + weight(w, v))
distv_min : {g : Graph gsize weight ops} ->
            (cl : Column len g src) ->
            Type
distv_min cl {g} {gsize}
  = (v, w : Node gsize) ->
    (exp_w : explored w cl) ->
    dgte ops (nodeDistN v cl) (dplus ops (edgeW g w v) (nodeDistN w cl)) = False


-- statement 4 :  distn+1[v] = δ(v) similar to stm of lemma 3
expDistIsDelta : {g : Graph gsize weight ops} ->
                 (cl : Column len g src) ->
                 Type
expDistIsDelta cl {g} {gsize} {ops} {src}
  = (v : Node gsize) ->
    (exp : explored v cl) ->
    (psv : Path src v g) ->
    (sp : shortestPath g psv) ->
    dEq ops (nodeDistN v cl) (length psv) = True



-- all three statements for lemma 5
l5_stms : {g : Graph gsize weight ops} ->
          (cl : Column len g src) ->
          Type
l5_stms cl = (lessDInf cl, unexpDelta cl, distv_min cl, expDistIsDelta cl)


l5_sp : {cl : Column len g src} ->
        (stms : l5_stms cl) ->
        expDistIsDelta cl
l5_sp (s1, s2, s3, s4) = s4



l5_stm1 : {g : Graph gsize weight ops} ->
          (cl : Column (S len) g src) ->
          (l5_ih : l5_stms cl) ->
          lessDInf (runHelper cl)
l5_stm1 cl (ih1, ih2, ih3, ih4) v expVR with (getMin cl == v) proof min_is_v
  | True = ?l51t
  | False = dgteDInfTrans (nodeDistN v cl) (nodeDistN v (runHelper cl)) (ih1 v (expV_VNotMin cl v expVR (nodeNotEq {a=getMin cl} {b=v} $ sym min_is_v))) (runDecre cl v)




l5_stm2 : {g : Graph gsize weight ops} ->
          (cl : Column (S len) g src) ->
          (l5_ih : l5_stms cl) ->
          unexpDelta (runHelper cl)
l5_stm2 cl (ih1, ih2, ih3, ih4) v v' expVR unexpVR' psv' spsv' -- (Cons psw v' adj_wv') spsv'
  with (getMin cl == v) proof min_is_v
    | True = ?l5t
    {- with (adj_getPrev adj_wv')
        | w with (checkUnexplored w cl) proof w_exp
          | Yes unexpW = ?l2y
          | No expW = ?l2n-}
    | False = dgteComm (ih2 v v' (expV_VNotMin cl v expVR (nodeNotEq {a=getMin cl} {b=v} $ sym min_is_v)) (unexpReverse cl v' unexpVR') psv' spsv') --(Cons psw v' adj_wv') spsv')
                       (runDecre cl v)



l5_stm3 : {g : Graph gsize weight ops} ->
          (cl : Column (S len) g src) ->
          (l2_ih : neDInfPath cl) ->
          (l5_ih : l5_stms cl) ->
          distv_min (runHelper cl)
l5_stm3 cl l2_ih (ih1, ih2, ih3, ih4) v w expW = ?l3
{-
  with (getMin cl == w) proof min_is_w
    | True = ?l3t
    | False = dgteAscTF (ih3 v w (expV_VNotMin cl w expW (nodeNotEq {a=getMin cl} {b=w} $ sym min_is_w)) psw sp_psw adj_wv) (runDecre cl v)
-}


l5_stm4 : {g : Graph gsize weight ops} ->
          (cl : Column (S len) g src) ->
          (l2_ih : neDInfPath cl) ->
          (st1 : lessDInf (runHelper cl)) ->
          (st2 : unexpDelta (runHelper cl)) ->
          (st3 : distv_min (runHelper cl)) ->
          (l5_ih : l5_stms cl) ->
          expDistIsDelta (runHelper cl)
l5_stm4 cl l2_ih st1 st2 st3 l5_ih v expVR {src=v} (Unit _ _) spsv = ?l5_unit
l5_stm4 cl l2_ih st1 st2 st3 (ih1, ih2, ih3, ih4) v expVR (Cons psw v adj_wv) spsv {g} {ops} {src}
  with (getMin cl == v) proof min_is_v
    | True with (l2_existPath cl l2_ih v (st1 v expVR))
      | (lpsv ** rclvEq) with (adj_getPrev adj_wv)
        | w with (checkUnexplored w (runHelper cl)) proof w_exp
          | Yes unexpW = dgteEq (dgteEqTrans rclvEq True (spsv lpsv))
                                (dgtePlus (DVal (get_weight (getNeighbors g w) v adj_wv))
                                          (st2 v w expVR unexpW psw (l1_prefixSP {sp=Cons psw v adj_wv} {sp_pre = psw} spsv ((adj_to_path adj_wv) ** Refl))))
          | No expW with (v == w) proof v_is_w
            | True = ?l54t
            | False = absurd $ contradict (dgteEqTrans rclvEq True (spsv lpsv))
                                              (dgtePlusEqFst {d1=nodeDistN v (runHelper cl)}
                                                       {d2=nodeDistN w (runHelper cl)}
                                                       {d3=length psw}
                                                       (DVal $ get_weight (getNeighbors g w) v adj_wv)-- (edgeW g w v)
                                                       False
                                                       (rewrite (sym $ edgeWEq g w v adj_wv) in (st3 v w expW))
                                                       (l3_preserveDelta cl l2_ih w psw
                                                         (l1_prefixSP {sp=Cons psw v adj_wv} {sp_pre = psw} spsv ((adj_to_path adj_wv) ** Refl))
                                                         (ih4 w (expV_VNotMin cl w expW (nodeNotEqTrans (nodeEq {a=getMin cl} {b=v} $ sym min_is_v) (nodeNotEq {a=v} {b=w} $ sym v_is_w)))
                                                                psw
                                                                (l1_prefixSP {sp=Cons psw v adj_wv} {sp_pre = psw} spsv ((adj_to_path adj_wv) ** Refl)))))


               {-absurd $ contradict (dgteEqTrans rclvEq True (spsv lpsv))
                                           (st3 v w expW psw
                                             (l1_prefixSP {sp=Cons psw v adj_wv} {sp_pre = psw} spsv ((adj_to_path adj_wv) ** Refl))
                                             adj_wv)-}
    | False with (l2_existPath cl l2_ih v (st1 v expVR))
      | (path_sv ** rclvEq) = dgteEq (dgteEqTrans rclvEq True (spsv path_sv))
                                     (dgteEqTrans
                                       (dEqComm $ ih4 v (expV_VNotMin cl v expVR (nodeNotEq {a=getMin cl} {b=v} $ sym min_is_v)) (Cons psw v adj_wv) spsv)
                                       True (runDecre cl v))




l5_spath : {g : Graph gsize weight ops} ->
           (cl : Column (S len) g src) ->
           (l2_ih : neDInfPath cl) ->
           (l5_ih : l5_stms cl) ->
           l5_stms (runHelper cl)
l5_spath cl l2_ih l5_ih
  = (l5_stm1 cl l5_ih,
     l5_stm2 cl l5_ih,
     l5_stm3 cl l2_ih l5_ih,
     l5_stm4 cl l2_ih (l5_stm1 cl l5_ih) (l5_stm2 cl l5_ih) (l5_stm3 cl l2_ih l5_ih) l5_ih)
{-(pf1, pf2, pf3)
  where
    pf1 p = ?pf1

    pf2 p = ?pf2

    pf3 p = ?pf3 ... (pf1 p) ... (pf2 p) ...
-}







{- proof of correctness -}
correctness : {g : Graph gsize weight ops} ->
              (cl : Column len g src) ->
              (l2_ih : neDInfPath cl) ->
              (l5_ih : l5_stms cl) ->
              l5_stms (runDijkstras cl)
correctness {len = Z} cl l2_ih l5_ih = l5_ih
correctness {len=S n} cl@(MKColumn g src (S n) unexp dist) l2_ih l5_ih
  = ?crt--correctness (runHelper {len=n} cl) (l2_existPath cl l2_ih) (l5_spath cl l2_ih l5_ih)



dijkstras_correctness : (gsize : Nat) ->
                        (g : Graph gsize weight ops) ->
                        (src : Node gsize) ->
                        (v : Node gsize) ->
                        (psv : Path src v g) ->
                        (spsv : shortestPath g psv) ->
                        dEq ops (indexN (finToNat (getVal v)) (dijkstras gsize g src) {p=nvLTE {gsize=gsize} (getVal v)}) (length psv) = True
dijkstras_correctness Z g src _ _ _ = absurd $ NodeZAbsurd src
dijkstras_correctness (S len) g src v psv spsv {weight} {ops}
  = ?dijk--(l5_sp {cl=runDijkstras col} (correctness col lemma2_ih base_stm)) v ?exp psv spsv
  where
    nodes : Vect (S len) (Node (S len))
    nodes = mknodes (S len) (S len) lteRefl (rewrite (minusRefl {a=S len}) in Nil)
    dist : Vect (S len) (Distance weight)
    dist = mkdists (S len) src ops
    col : Column (S len) g src
    col = (MKColumn g src (S len) nodes dist)
    lemma2_ih : neDInfPath col
    lemma2_ih v notInf = ?lemma2
    base_stm : l5_stms col
    base_stm = ?base


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














{-
{- if `dist_v` is smaller than DInf, then `dist_v` is equal to the length of some path-}
distNotInfIsPathLen : {g : Graph gsize weight ops} ->
                      (cl : Column len g src) ->
                      (v : Node gsize) ->
                      (ne : dgte ops (nodeDistN v cl) DInf = False) ->
                      (psv : Path src v g ** dEq ops (nodeDistN v cl) (length psv) = True)
distNotInfIsPathLen cl v ne = ?dpath
-}



{-==================older versions of calcDist and updateDist ==============-}
{-

calcDist : (g : Graph gsize weight ops) ->
           (minN : Node gsize) ->
           (cur : Node gsize) ->
           (old : Vect gsize (Distance weight)) ->
           Distance weight
calcDist g minN cur old {ops}
  = min ops (index (getVal cur) old)
              (dplus ops (index (getVal minN) old) (edgeW g minN cur))


updateDist :  (g : Graph gsize weight ops) ->
              (min : Node gsize) ->
              (nodes : Vect m (Node gsize)) ->
              (dist : Vect gsize (Distance weight)) ->
              Vect m (Distance weight)
updateDist g min Nil dist = Nil
updateDist g min (x :: xs) dist = (calcDist g min x dist) :: (updateDist g min xs dist)






updateDistV4 :(g : Graph gsize weight ops) ->
              (min_node : Node gsize) ->
              (minD : Distance weight) ->
              (n : Nat) ->
              (nodes : Vect m (Node gsize)) ->
              (dist : Vect m (Distance weight)) ->
              Vect m (Distance weight)
updateDistV4 g _ _ _ Nil Nil = Nil
updateDistV4 g min_node md Z (nd :: ns) (d :: ds) = (calcDistV4 g min_node nd md d) :: ds
updateDistV4 g min_node md (S n) (nd :: ns) (d :: ds)
  = updateDistV4 g min_node md n (nd :: ns) (d :: updateDistV4 g min_node md n ns ds)



updateDistV5 :(g : Graph gsize weight ops) ->
              (min_node : Node gsize) ->
              (minD : Distance weight) ->
              (n, m : Nat) ->
              {auto p : LTE m gsize} ->
              (dist : Vect m (Distance weight)) ->
              Vect m (Distance weight)
updateDistV5 g mn md _ Z Nil = Nil
updateDistV5 g mn md Z (S len) dist@(d :: ds) {gsize} {p}
  = (calcDistV4 g mn (MKNode (natTofin (minus gsize (S len)) gsize {p=lteMinus gsize len p})) md d) :: ds
updateDistV5 g mn md (S n) (S len) (d :: ds) {p}
  = updateDistV5 g mn md n (S len) $ d :: (updateDistV5 g mn md n len ds {p=lteSuccLeft p})
{-
updateDistV5 :(g : Graph gsize weight ops) ->
              (min_node : Node gsize) ->
              (minD : Distance weight) ->
              (sum : Fin gsize) ->
              (n, m: Fin gsize) ->
              {auto p : n + m = gsize} ->
              (dist : Vect len (Distance weight)) ->
              Vect len (Distance weight)
updateDistV5 g _ _ _ _ Nil = Nil
updateDistV5 g min_node md Z gsize (d :: ds) = (calcDistV4 g min_node (MKNode (natTofin gsize gsize) {p=lteRefl}) md d) :: ds
updateDistV5 g min_node md (S n) m (d :: ds)
  = updateDistV5 g min_node md n (S m) (d :: (updateDistV5 g min_node md n f ds))
-}





{- `updateEq` and `udEq` are helper proofs for `naDistEq`,
as `runHelper` is defined with `updateDist` and `calcDist`.  -}

udEq : (g : Graph gsize weight ops) ->
       (m, c : Node gsize) ->
       (old : Vect gsize (Distance weight)) ->
       (na : Not (adj g m c)) ->
       dEq ops (looseIndex (getVal c) old DInf) (calcDist g m c old) = True
udEq g m c old na {ops} = ?upeq{-with (edgeW g m c) proof isAdj
  | (DVal w) = ?lllt--absurd $ na (edgeW_adj {w=w} (sym isAdj))
  | DInf with (dgte ops (index (getVal c) old) (dplus ops (index (getVal m) old) DInf)) proof dgt
      | True = ?fff
      | False = dEqRefl-}


udEqV4 : (g : Graph gsize weight ops) ->
         (min_node : Node gsize) ->
         (cur : Node gsize) ->
         (min_dist : Distance weight) ->
         (cur_dist : Distance weight) ->
         (na : Not (adj g min_node cur)) ->
         dEq ops cur_dist (calcDistV4 g min_node cur min_dist cur_dist) = True


updateEq : (g : Graph gsize weight ops) ->
           (mn : Node gsize) ->
           --(nodes : Vect gsize (Node gsize)) ->
           (dist : Vect gsize (Distance weight)) ->
           (nv : Fin gsize) ->
           --(e : Elem (MKNode nv) nodes) ->
           -- should be (gsize - nv)
           (na : Not (adj g mn (MKNode nv))) ->
           dEq ops (looseIndex nv dist DInf) (looseIndex nv (updateDistV5 g mn (index (getVal mn) dist) gsize gsize dist {p=lteRefl}) DInf) = True
           --dEq ops (looseIndex nv dist DInf) (looseIndex nv (updateDistV4 g mn (index (getVal mn) dist) gsize nodes dist) DInf) = True
           --dEq ops (looseIndex nv dist DInf) (looseIndex nv (updateDistV1 g mn gsize dist {p=lteRefl}) DInf) = True
           --dEq ops (looseIndex nv dist DInf) (looseIndex nv (updateDist g mn nodes dist) DInf) = True
--updateEq g mn Nil dist nv na = absurd $ NodeZAbsurd mn
updateEq  g mn (d :: ds) FZ na = ?base --udEqV4 g mn (MKNode FZ) (index (getVal mn) (d :: ds)) d na
updateEq  g mn (d :: ds) (FS f) na = ?recur --absurd $ FinZAbsurd f
--updateEq {gsize = S (S len)} g mn (d :: ds) FZ na = ?
--updateEq {gsize = S (S len)} g mn (d :: ds) (FS f) na = ?fsfs --updateEq g mn len xs dist e na {p=lteSuccLeft p}

--
-- updateEq : (g : Graph gsize weight ops) ->
--            (mn : Node gsize) ->
--            (dist : Vect gsize (Distance weight)) ->
--            (nv : Fin gsize) ->
--            --(e : Elem (MKNode nv) nodes) ->
--            -- should be (gsize - nv)
--            (na : Not (adj g mn (MKNode nv))) ->
--            dEq ops (looseIndex nv dist DInf) (looseIndex nv (updateDist0 g mn (index (getVal mn) dist) gsize dist {p=lteRefl}) DInf) = True
-- updateEq g mn dist FZ na = ?base --udEq g mn (MKNode nv) dist na
-- updateEq g mn (d :: ds) (FS f) na = ?upth --updateEq g mn len xs dist e na {p=lteSuccLeft p}



naDistEq : {g : Graph gsize weight ops} ->
           (cl : Column (S len) g src) ->
           (v : Node gsize) ->
           (ne: Not (adj g (getMin cl) v)) ->
           dEq ops (index (getVal c) (cdist cl)) (index (getVal c) (cdist $ runHelper cl)) = True
naDistEq {g} {gsize} cl@(MKColumn g src (S len) unexp dist) v ne
  = ?ll--updateEq g (getMin cl) (mkNodes gsize) (cdist cl) ne

-}



{- =================== older versions ====================-}
{- older version
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




{- replace hard to work with
updateDist :  (g : Graph gsize weight ops) ->
              (cur : Node gsize) ->
              (nodes : Vect m (Node gsize)) ->
              {auto p : LTE m gsize} ->
              (dist : Vect gsize (Distance weight)) ->
              Vect gsize (Distance weight)
updateDist g cur Nil dist = dist
updateDist g cur (x :: xs) dist {p}
  = updateDist g cur xs (replaceAt (getVal x) (calcDist g cur x dist) dist) {p=lteSuccLeft p}
  -}

{- this version does not work
-- uphelper :  (g : Graph gsize weight ops) ->
--               (min : Node gsize) ->
--               (minD : Distance weight) ->
--               (nv : Fin gsize) ->
--               (dist : Vect gsize (Distance weight)) ->
--               Vect gsize (Distance weight)
-- uphelper g min minD FZ (x :: xs) = (calcDist g min x dist) :: xs
-- uphelper g min minD (FS f) (x :: xs) = uphelper g minD f $ x :: (uphelper g minD f xs)
--
-- updateDist0 : (g : Graph gsize weight ops) ->
--               (min : Node gsize) ->
--               (nv : Fin gsize) ->
--               (dist : Vect gsize (Distance weight)) ->
--               Vect gsize (Distance weight)
-- updateDist0 g min FZ (x :: xs) = (calcDist g min x dist) :: xs
-- updateDist0 g min (FS f) dist = updateDist0 g min f $ uphelper g min (FS f) dist
-}
{- working version 2 hard to work with rewrite
updateDistV1 : (g : Graph gsize weight ops) ->
              (min : Node gsize) ->
              (n : Nat) ->
              {auto p : LTE n gsize} ->
              (dist : Vect gsize (Distance weight)) ->
              Vect n (Distance weight)
updateDistV1 g min Z dist = Nil
updateDistV1 g min (S n) dist {p} {gsize}
  = rewrite (sym $ plusCommutative n (S Z)) in
      (updateDistV1 g min n dist {p=lteSuccLeft p} ++
        ((calcDist g min (MKNode (natTofin n gsize)) dist) :: Nil))

-}

{- not working
updateDist0 g cur (x :: xs) old new {p} with (inNodeset x (getNeighbors g cur)) proof adj
  | True = updateDist0 g cur xs old
              (replaceAt (getVal x)
                (min ops (index (getVal x) old)
                  (dplus ops (index (getVal cur) old) (DVal $ edge_weight (sym adj))))
                  new) {p=lteSuccLeft p}
  | False = updateDist0 g cur xs old (replaceAt (getVal x) (index (getVal x) old) new) {p=lteSuccLeft p}



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
