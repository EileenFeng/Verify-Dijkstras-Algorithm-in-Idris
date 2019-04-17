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
using (weight : Type)
  record WeightOps weight where
    constructor MKWeight
    zero : weight
    gtew : weight -> weight -> Bool
    eq : weight -> weight -> Bool
    add : weight -> weight -> weight
    eqRefl : {w : weight} -> eq w w = True
    eqComm : {w1, w2 : weight} -> eq w1 w2 = True -> eq w2 w1 = True
    eqTrans : {w1, w2, w3 : weight} ->
              eq w1 w2 = True ->
              eq w2 w3 = True ->
              eq w1 w3 = True
    gteEq : {a, b : weight} ->
            (gtew a b = True) ->
            (gtew b a = True) ->
            eq a b = True
    gteRefl : {a : weight} -> (gtew a a = True)
    gteReverse : {a, b : weight} -> (p : gtew a b = False) -> gtew b a = True
    gteComm : {a, b, c : weight} ->
              (p1 : gtew a b = True) ->
              (p2 : gtew b c = True) ->
              gtew a c = True
    gteBothPlus : {a, b : weight} ->
                  (c : weight) ->
                  (p1 : gtew a b = False) ->
                  gtew (add a c) (add b c) = False
    gtePlus : {a, b : weight} ->
              (c : weight) ->
              gtew a b = True ->
              gtew (add c a) b = True
    gtePlusEq : {w1, w2, w3 : weight} ->
                (dp : weight) ->
                (b : Bool) ->
                (gtew (add dp w2) w1 = b) ->
                (eq w2 w3 = True) ->
                gtew (add dp w3) w1 = b
    triangle_ineq : (a : weight) -> (b : weight) -> gtew (add a b) a = True
    gtewEqTrans : {w1, w2, w3 : weight} -> (eq w1 w2 = True) -> (b : Bool) -> (gtew w2 w3 = b) -> gtew w1 w3 = b
    addComm : (a : weight) -> (b : weight) -> add a b = add b a
    --gtewPlusFalse : (a, b : weight) -> gtew a (add b a) = False


-- any value added to infinity should be infinity
-- need to define arithmetics for Distance type
data Distance : Type -> Type where
  DInf : Distance weight
  DVal : (val : weight) -> Distance weight


dEq : (ops : WeightOps weight) ->
      (Distance weight) ->
      (Distance weight) ->
      Bool
dEq _ DInf DInf = True
dEq _ DInf _ = False
dEq _ _ DInf = False
dEq ops (DVal v1) (DVal v2) = eq ops v1 v2


dEqRefl : {ops : WeightOps weight} ->
          {d : Distance weight} ->
          dEq ops d d = True
dEqRefl {d=DInf} = Refl
dEqRefl {d=DVal w} {ops} = eqRefl ops

{-
dEqTransTrue : {ops : WeightOps weight} ->
               {d1, d2, d3 : Distance weight} ->
               (dEq ops d1 d2 = True) ->
               (dEq ops d2 d3 = True) ->
               dEq ops d1 d3 = True



dEqTransTF : {ops : WeightOps weight} ->
             {d1, d2, d3 : Distance weight} ->
             (dEq ops d1 d2 = False) ->
             (dEq ops d2 d3 = True) ->
             dEq ops d1 d3 = False
-}



dEqComm : {ops : WeightOps weight} ->
          {d1, d2 : Distance weight} ->
          (dEq ops d1 d2 = True) ->
          dEq ops d2 d1 = True
dEqComm {d1=DInf} {d2=DInf} _ = Refl
dEqComm {d1=DVal v1} {d2=DInf} refl = absurd $ trueNotFalse (sym refl)
dEqComm {d1=DInf} {d2=DVal _} refl = absurd $ trueNotFalse (sym refl)
dEqComm {d1=DVal v1} {d2=DVal v2} refl {ops} = eqComm ops refl


dEqTrans : {ops : WeightOps weight} ->
           {d1, d2, d3 : Distance weight} ->
           (e1 : dEq ops d1 d2 = True) ->
           (e2 : dEq ops d2 d3 = True) ->
           dEq ops d1 d3 = True
dEqTrans {d1=DInf} {d2=DInf} {d3=DInf} e1 e2 = Refl
dEqTrans {d1=DInf} {d2=DInf} {d3=DVal _} e1 e2 = absurd $ trueNotFalse (sym e2)
dEqTrans {d1=DInf} {d2=DVal _} {d3=DInf} e1 e2 = absurd $ trueNotFalse (sym e1)
dEqTrans {d1=DVal _} {d2=DInf} {d3=DInf} e1 e2 = absurd $ trueNotFalse (sym e1)
dEqTrans {d1=DInf} {d2=DVal _} {d3=DVal _} e1 e2 = absurd $ trueNotFalse (sym e1)
dEqTrans {d1=DVal _} {d2=DInf} {d3=DVal _} e1 e2 = absurd $ trueNotFalse (sym e1)
dEqTrans {d1=DVal _} {d2=DVal _} {d3=DInf} e1 e2 = absurd $ trueNotFalse (sym e2)
dEqTrans {d1=DVal v1} {d2=DVal v2} {d3=DVal v3} e1 e2 {ops} = eqTrans ops e1 e2




-- plus for Distance type
dplus : (ops : WeightOps weight) ->
        (Distance weight) ->
        (Distance weight) ->
        (Distance weight)
dplus _ DInf _ = DInf
dplus _ _ DInf = DInf
dplus ops (DVal v1) (DVal v2) = DVal $ (add ops) v1 v2

-- greater than or equal to for Distance type
-- can we treat infinity as equal to infinity?
dgte : (ops : WeightOps weight) ->
       Distance weight ->
       Distance weight -> Bool
dgte _ DInf _ = True
dgte _ _ DInf = False
dgte ops (DVal v1) (DVal v2) = (gtew ops) v1 v2


-- smaller than
dlt : (ops : WeightOps weight) ->
      Distance weight ->
      Distance weight ->
      Bool
dlt ops d1 d2 = not $ dgte ops d1 d2




dplusDInf : {ops : WeightOps weight} ->
            {d : Distance weight} ->
            dplus ops d DInf = DInf
dplusDInf {d=DInf} = Refl
dplusDInf {d=DVal _} = Refl


{-
dgteDInfReduce : {ops : WeightOps weight} ->
                 {d1, d2 : Distance weight} ->
                 (dgte ops (dplus ops d1 d2) DInf = False) ->
                 dgte ops d2 DInf = False
-}


dgteZeroInf : {ops : WeightOps weight} ->
              dgte ops (DVal (zero ops)) DInf = False
dgteZeroInf = Refl


dgteDInfRefl : {ops : WeightOps weight} ->
               {d : Distance weight} ->
               dgte ops DInf d = True
dgteDInfRefl {d=DInf} = Refl
dgteDInfRefl {d=DVal _} = Refl


dgteRefl : dgte ops d d = True
dgteRefl {d = DInf} = Refl
dgteRefl {d= DVal dv} {ops} with (gtew ops dv dv) proof dvRefl
  | True = Refl
  | False = absurd $ contradict (gteRefl ops) (sym dvRefl)


-- d1 >= d2 -> d2 <= d1
dgteReverse : dgte ops d1 d2 = False -> dgte ops d2 d1 = True
dgteReverse {d1=DInf} Refl impossible
dgteReverse {d2=DInf} refl = Refl
dgteReverse {d1=DVal v1} {d2=DVal v2} {ops} refl = gteReverse ops refl


-- d3 <= d2, d2 <= d1 -> d3 <= d1
dgteComm : {ops : WeightOps weight} ->
           {d1, d2, d3 : Distance weight} ->
           dgte ops d1 d2 = True ->
           dgte ops d2 d3 = True ->
           dgte ops d1 d3 = True
dgteComm {d1=DInf} _ _ = Refl
dgteComm {d1=DVal _} {d2=DInf} r1 r2 = absurd $ trueNotFalse (sym r1)
dgteComm {d1=DVal _} {d2=DVal _} {d3=DInf} r1 r2 = absurd $ trueNotFalse (sym r2)
dgteComm {ops} {d1=DVal v1} {d2=DVal v2} {d3=DVal v3} r1 r2 = gteComm ops r1 r2


{-
dgteAscTF : {ops : WeightOps weight} ->
            {d1, d2, d3 : Distance weight} ->
            dgte ops d2 d1 = False ->
            dgte ops d2 d3 = True ->
            dgte ops d3 d1 = False
-}



-- d2 <= d1 -> d2 + (DVal w) <= d1 + (DVal w)
dgteBothPlus : {d1, d2: Distance weight} ->
               {ops : WeightOps weight} ->
               (w : weight) ->
               dgte ops d1 d2 = False ->
               dgte ops (dplus ops (DVal w) d1) (dplus ops (DVal w) d2) = False
dgteBothPlus {d1=DInf} {d2} _ Refl impossible
dgteBothPlus {d1=DVal v1} {d2=DInf} w refl = Refl
dgteBothPlus {d1=DVal v1} {d2=DVal v2} w refl {ops}
  = rewrite (addComm ops w v1) in (rewrite (addComm ops w v2) in (gteBothPlus ops w refl))





-- d2 <= d1, d1 <= DInf -> d2 <= DInf
dgteDInfTrans : (d1, d2 : Distance weight) ->
                {ops : WeightOps weight} ->
                (p1 : dgte ops d1 DInf = False) ->
                (p2 : dgte ops d1 d2 = True) ->
                dgte ops d2 DInf = False
dgteDInfTrans DInf DInf p1 p2 = absurd $ trueNotFalse p1
dgteDInfTrans DInf (DVal w) p1 p2 = absurd $ trueNotFalse p1
dgteDInfTrans (DVal w1) (DInf) p1 p2 = absurd $ trueNotFalse (sym p2)
dgteDInfTrans (DVal w1) (DVal w2)  _ p2 = Refl



-- d1 = d2, d3 <= d2 -> d3 <= d1
dgteEqTrans : {ops : WeightOps weight} ->
              {d1, d2, d3 : Distance weight} ->
              (eq : dEq ops d1 d2 = True) ->
              (b : Bool) ->
              (dgeq : dgte ops d2 d3 = b) ->
              dgte ops d1 d3 = b
dgteEqTrans {d1=DInf} {d2=DInf} {d3=DInf} eq True refl = Refl
dgteEqTrans {d1=DInf} {d2=DInf} {d3=DInf} eq False refl = absurd $ trueNotFalse refl
dgteEqTrans {d1=DInf} {d2=DInf} {d3=DVal w} eq True refl = Refl
dgteEqTrans {d1=DInf} {d2=DInf} {d3=DVal w} eq False refl = absurd $ trueNotFalse refl
dgteEqTrans {d1=DInf} {d2=DVal val} {d3} eq _ _ = absurd $ trueNotFalse (sym eq)
dgteEqTrans {d1=DVal w} {d2=DInf} {d3} eq _ _ = absurd $ trueNotFalse (sym eq)
dgteEqTrans {d1=DVal w1} {d2=DVal w2} {d3=DInf} eq True refl = absurd $ trueNotFalse (sym refl)
dgteEqTrans {d1=DVal w1} {d2=DVal w2} {d3=DInf} eq False refl = Refl
dgteEqTrans {d1=DVal w1} {d2=DVal w2} {d3=DVal w3} deq b refl {ops} = gtewEqTrans ops deq b refl



{-
-- d1 <= d2, d1 >= d3 -> d3 <= d2
dgteTrans : {ops : WeightOps weight} ->
            {d1, d2, d3 : Distance weight} ->
            (dgte1 : dgte ops d1 d2 = False) ->
            (dgte2 : dgte ops d1 d3 = True) ->
            dgte ops d3 d2 = False
-}



-- d2 <= d1, d1 <= d2 -> d1 = d2
dgteEq : {ops : WeightOps weight} ->
         {d1, d2 : Distance weight} ->
         (e1 : dgte ops d1 d2 = True) ->
         (e2 : dgte ops d2 d1 = True) ->
         dEq ops d1 d2 = True
dgteEq {d1=DInf} {d2=DInf} e1 e2 = Refl
dgteEq {d1=DInf} {d2=DVal w2} e1 e2 = e2
dgteEq {d1=DVal w1} {d2=DInf} e1 e2 = e1
dgteEq {d1=DVal w1} {d2=DVal w2} e1 e2 {ops} = gteEq ops e1 e2




dgtePlus : {ops : WeightOps weight} ->
           {d1, d2 : Distance weight} ->
           (d3 : Distance weight) ->
           (e1 : dgte ops d1 d2 = True) ->
           dgte ops (dplus ops d3 d1) d2 = True
dgtePlus {d1=DInf} {d2=DInf} DInf e = e
dgtePlus {d1=DInf} {d2=DInf} (DVal _) e = e
dgtePlus {d1=DInf} {d2=DVal w} DInf e = Refl
dgtePlus {d1=DInf} {d2=DVal w} (DVal _) e = Refl
dgtePlus {d1=DVal _} {d2= DInf} d3 e = absurd $ trueNotFalse (sym e)
dgtePlus {d1=DVal v1} {d2=DVal v2} DInf e = Refl
dgtePlus {d1=DVal v1} {d2=DVal v2} (DVal v3) e {ops} = gtePlus ops v3 e



dgtePlusEq : {ops : WeightOps weight} ->
             {d1, d2, d3 : Distance weight} ->
             (dv_plus : Distance weight) ->
             (b : Bool) ->
             (dgte ops (dplus ops dv_plus d2) d1= b) ->
             (eq : dEq ops d2 d3 = True) ->
             dgte ops (dplus ops dv_plus d3) d1 = b
dgtePlusEq DInf True de e = Refl
dgtePlusEq DInf False de e = absurd $ trueNotFalse de
dgtePlusEq {d1=DInf} {d2=DInf} {d3=DInf} (DVal val) True de e = Refl
dgtePlusEq {d1=DInf} {d2=DInf} {d3=DInf} (DVal val) False de e = de
dgtePlusEq {d1=DVal d1} {d2=DInf} {d3=DInf} (DVal val) True de e = Refl
dgtePlusEq {d1=DVal d1} {d2=DInf} {d3=DInf} (DVal val) False de e = de
dgtePlusEq {d1=DInf} {d2=DVal d2} {d3=DInf} (DVal val) True de e = Refl
dgtePlusEq {d1=DInf} {d2=DVal d2} {d3=DInf} (DVal val) False de e = sym e
dgtePlusEq {d1=DInf} {d2=DInf} {d3=DVal d3} (DVal val) True de e = e
dgtePlusEq {d1=DInf} {d2=DInf} {d3=DVal d3} (DVal val) False de e = Refl
dgtePlusEq {d1=DVal d1} {d2=DVal d2} {d3=DInf} (DVal val) True de e = Refl
dgtePlusEq {d1=DVal d1} {d2=DVal d2} {d3=DInf} (DVal val) False de e = sym e
dgtePlusEq {d1=DVal d1} {d2=DInf} {d3=DVal d3} (DVal val) True de e = absurd $ trueNotFalse (sym e)
dgtePlusEq {d1=DVal d1} {d2=DInf} {d3=DVal d3} (DVal val) False de e = absurd $ trueNotFalse de
dgtePlusEq {d1=DInf} {d2=DVal d2} {d3=DVal d3} (DVal val) True de e = de
dgtePlusEq {d1=DInf} {d2=DVal d2} {d3=DVal d3} (DVal val) False de e = Refl
dgtePlusEq {d1=DVal d1} {d2=DVal d2} {d3=DVal d3} (DVal val) b de e {ops} = gtePlusEq ops val b de e


{-
dgtePlusEq {d1=DVal d1} {d2=DInf} {d3=DInf} (DVal dp) True de e = ?dd5
dgtePlusEq {d1=DVal d1} {d2=DInf} {d3=DInf} (DVal dp) False de e = ?dd6
dgtePlusEq {d1=DInf} {d2=DVal d2} {d3=DInf} (DVal dp) True de e = ?dd7
dgtePlusEq {d1=DInf} {d2=DVal d2} {d3=DInf} (DVal dp) False de e = ?dd71
dgtePlusEq {d1=DInf} {d2=DInf} {d3=DVal d3} (DVal dp) True de e = ?dd12
dgtePlusEq {d1=DInf} {d2=DInf} {d3=DVal d3} (DVal dp) False de e = ?dd13
dgtePlusEq {d1=DInf} {d2=DVal d2} {d3=DInf} (DVal dp) True de e = ?dd14
dgtePlusEq {d1=DInf} {d2=DVal d2} {d3=DInf} (DVal dp) False de e = ?dd15
-}



dgtePlusDInf: {ops : WeightOps weight} ->
              {dp_val, d : Distance weight} ->
              dgte ops (dplus ops dp_val d) DInf = False ->
              dgte ops d DInf = False
dgtePlusDInf {dp_val = DInf} {d=DInf} e1 = e1
dgtePlusDInf {dp_val=DInf} {d=DVal _} e1 = absurd $ trueNotFalse e1
dgtePlusDInf {dp_val=DVal _} {d=DInf} e1 = absurd $ trueNotFalse e1
dgtePlusDInf {dp_val=DVal d1} {d=DVal d2} e1 = Refl



dgteReplace : {ops : WeightOps weight} ->
              {d1, d2, d3 : Distance weight} ->
              (b : Bool) ->
              (neq : dgte ops d1 d3 = b) ->
              (deq : d1 = d2) ->
              dgte ops d2 d3 = b
dgteReplace b neq deq = rewrite (sym deq) in neq

{-
dgtePlusAbsurd : {ops : WeightOps weight} ->
                 (d1, d2 : Distance weight) ->
                 dgte ops d1 (dplus ops d2 d1) = False
dgtePlusAbsurd (DVal d1) DInf = Refl
dgtePlusAbsurd DInf d2 = ?dpa1
dgtePlusAbsurd (DVal v1) (DVal v2) {ops}
  with (gtew ops v1 (add ops v2 v1)) proof notTrue
    | True = absurd $ contradict (sym notTrue) (gtewPlusFalse ops v1 v2)
    | False = Refl
-}

-- d1 <= DInf -> d1 + (DVal w) <= DInf
dvalNotInf : {ops : WeightOps weight} ->
             {d1 : Distance weight} ->
             {w : weight} ->
             (dgte ops d1 DInf = False) ->
             dgte ops (dplus ops (DVal w) d1) DInf = False
dvalNotInf {d1=DInf} refl = absurd $ trueNotFalse refl
dvalNotInf {d1=DVal v1} {w} refl = Refl





{-
dInfRefl : dgte ops DInf DInf = True
dInfRefl = Refl

dgte_false_notEq : dgte ops d1 d2 = False -> Not (d1 = d2)
dgte_false_notEq {d1=DInf} {d2=DInf} refl e = ?df2 --absurd $ trueNotFalse refl
dgte_false_notEq {d1=DInf} {d2} {ops} refl e = ?df1 --rewrite (rewrite (sym e) in refl) in dInfRefl
dgte_false_notEq {d2=DInf} refl e = ?df2
dgte_false_notEq {d1= DVal v1} {d2=DVal v2} refl e = ?df3
-}



data Node : (gsize : Nat) -> Type where
  MKNode : (nv : Fin gsize) -> Node gsize


implementation Uninhabited  (Node Z) where
  uninhabited (MKNode f) impossible


{- type `Node Z` is impossible -}
NodeZAbsurd : Node Z -> Void
NodeZAbsurd (MKNode f) impossible


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



nvLTE : {gsize : Nat} ->
        (nv : Fin gsize) ->
        LTE (S (finToNat nv)) gsize
nvLTE {gsize=Z} nv = absurd $ FinZAbsurd nv
nvLTE {gsize=S g} FZ = LTESucc LTEZero
nvLTE {gsize=S g} (FS f) = LTESucc $ nvLTE {gsize=g} f


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
nodeEq : {a, b : Node gsize} ->
         (a == b) = True ->
         (a = b)
nodeEq {a=MKNode av} {b=MKNode bv} refl = cong $ finEq av bv refl



nodeNotEq : {a, b : Node gsize} ->
            (a == b) = False ->
            Not (a = b)
nodeNotEq {a=MKNode av} {b=MKNode bv} refl ne
  = absurd $ contradict (finEqReverse $ NodeInjective ne) refl


nodeEqTrans : {a, b, c : Node gsize} ->
              (e1 : a = b) ->
              (e2 : b = c) ->
              a = c
nodeEqTrans e1 e2 = rewrite (sym e2) in e1


nodeNotEqTrans : {a, b, c : Node gsize} ->
                 (eq : a = b) ->
                 (neq : Not (b = c)) ->
                 Not (a = c)
nodeNotEqTrans e1 ne eac = absurd $ ne (rewrite (sym e1) in eac)



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
nodeNeq {a=MKNode av} {b=MKNode bv} refl e = finNeq refl (NodeInjective e)


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
data Graph : Nat -> (w : Type) -> (WeightOps w)-> Type where
  MKGraph : (gsize : Nat) ->
            (weight : Type) ->
            (ops : WeightOps weight) ->
            (edges : Vect gsize (nodeset gsize weight)) ->
            Graph gsize weight ops


{-give the edges of a certain node 'n' in graph 'g' -}
getNeighbors : (g : Graph gsize weight ops) ->
               (n : Node gsize) ->
               (nodeset gsize weight)
getNeighbors (MKGraph _ _ _ edges) (MKNode nv) = index nv edges



{- there is an edge from node 'n' to node 'm' -}
adj : (g : Graph gsize weight ops) ->
      (n, m : Node gsize) -> Type
adj g n m = (inNodeset m (getNeighbors g n) = True)


adj_getPrev : {g : Graph gsize weight ops} ->
              {n, m : Node gsize} ->
              (adj_nm : adj g n m) ->
              Node gsize
adj_getPrev adj {n} = n



adj_sameNode : {g : Graph gsize weight ops} ->
               {n, m : Node gsize} ->
               (eq : m = n) ->
               (adj_nm : inNodeset m (getNeighbors g n) = True) ->
               adj g n n
adj_sameNode {g} {n} {m} eq refl = ?adjSN


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
edge_weight : {g : Graph gsize weight ops} ->
              {n : Node gsize} ->
              {m : Node gsize} ->
              (adj g n m) ->
              weight
edge_weight {g} {n} {m} adj = get_weight (getNeighbors g n) m adj



edgeW : (g : Graph gsize weight ops) ->
        (n : Node gsize) ->
        (m : Node gsize) ->
        Distance weight
edgeW g n m with (inNodeset m (getNeighbors g n)) proof isAdj
  | True = DVal $ edge_weight (sym isAdj)
  | False = DInf


edgeWEq : (g : Graph gsize weight ops) ->
          (n : Node gsize) ->
          (m : Node gsize) ->
          (adj_nm : adj g n m) ->
          (edgeW g n m) = (DVal $ get_weight (getNeighbors g n) m adj_nm)
edgeWEq g n m adj_nm = ?edgeEq





  {- path without distance in Type -}

data Path : Node gsize ->
            Node gsize ->
            Graph gsize weight ops -> Type where
  Unit : (g : Graph gsize weight ops) ->
         (n : Node gsize) ->
         Path n n g
  Cons : Path s v g ->
         (n : Node gsize) ->
         (adj : adj g v n) ->
         Path s n g



{- length of path -}
length : {g : Graph gsize weight ops} ->
         Path s v g ->
         Distance weight
length (Unit _ _) {ops} = DVal $ zero ops
length (Cons p v adj) {ops}
  = dplus ops (DVal $ edge_weight adj) (length p)



adj_to_path : adj g n m -> Path n m g
adj_to_path adj {n} {m} {g} = Cons (Unit g n) m adj




append : Path s v g ->
         Path v w g ->
         Path s w g
append p (Unit _ w) = p
append p (Cons p1 w adj) = Cons (append p p1) w adj

{- prefix of a path -}
pathPrefix : (pprefix : Path s w g) ->
             (p : Path s v g) ->
             Type
pathPrefix pprefix p {w} {v} {g} = (ppost : Path w v g ** append pprefix ppost = p)



{- shortest path -}
-- `sp` stands for shortest path, `lp` stands for any other path
-- this definition seems inaccurate as `lp` refers to a specific s-v path rather than any s-v path in g
shortestPath : (g : Graph gsize weight ops) ->
               (sp : Path s v g) ->
               Type
shortestPath g sp {ops} {v}
  = (lp : Path s v g) ->
    dgte ops (length lp) (length sp) = True




-- connected Graph
connected : (g : Graph gsize weight ops) ->
            (v, w : Node gsize) ->
            Type
connected g v w = Path v w g


-- example with Nat as weight
n0 : Node 4
n0 = MKNode FZ

n1 : Node 4
n1 = MKNode (FS FZ)

n2 : Node 4
n2 = MKNode (FS (FS FZ))

n3 : Node 4
n3 = MKNode (FS (FS (FS FZ)))



set0 : nodeset 4 Nat
set0 = [(n2, 5), (n1, 1), (n3, 6)]

set1 : nodeset 4 Nat
set1 = [(n0, 2), (n2, 2), (n3, 7)]

set2 : nodeset 4 Nat
set2 = [(n3, 1)]

set3 : nodeset 4 Nat
set3 = Nil


set0' : nodeset 4 Nat
set0' = [(n2, 5), (n1, 1), (n3, 6)]

set1' : nodeset 4 Nat
set1' = [(n0, 2), (n2, 2), (n3, 7)]

set2' : nodeset 4 Nat
set2' = [(n3, 1)]

set3' : nodeset 4 Nat
set3' = [(n2, 6), (n1, 1)]




nat_gteRefl : gte a a = True
nat_gteRefl {a=Z} = Refl
nat_gteRefl {a=S a'} = nat_gteRefl {a=a'}


nat_gte_reverse : {a, b : Nat} -> gte a b = False -> gte b a = True
nat_gte_reverse {a=Z} {b=Z} refl = Refl
nat_gte_reverse {a=Z} {b=S _} refl = Refl
nat_gte_reverse {a=S _} {b=Z} Refl impossible
nat_gte_reverse {a=S a'} {b=S b'} refl = nat_gte_reverse {a=a'} {b=b'} refl


nat_gte_comm : {a, b, c : Nat} ->
               gte a b = True ->
               gte b c = True ->
               gte a c = True
--nat_gte_comm {a=Z} {b=Z} {c=Z}
nat_gte_comm {a=Z} {b=Z} {c=Z} _ _ = Refl
nat_gte_comm {b=Z} {c=S _} r1 r2 = absurd $ trueNotFalse (sym r2)
nat_gte_comm {a=Z} {b=S _} r1 r2 = absurd $ trueNotFalse (sym r1)
nat_gte_comm {a=S _} {b=S _} {c=Z} _ _ = Refl
nat_gte_comm {a=S _} {b=Z} {c=Z} _ _ = Refl
nat_gte_comm {a=S a'} {b=S b'} {c=S c'} r1 r2 = nat_gte_comm {a=a'} {b=b'} r1 r2


nat_gteBothPlus : {a, b : Nat} ->
                  (c : Nat) ->
                  (p : gte a b = False) ->
                  gte (plus a c) (plus b c) = False
nat_gteBothPlus Z p {a} {b}= rewrite (plusZeroRightNeutral a) in (rewrite (plusZeroRightNeutral b) in p)
nat_gteBothPlus (S c) p {a} {b}
  = rewrite (sym $ plusSuccRightSucc b c) in
            (rewrite (sym $ plusSuccRightSucc a c) in (nat_gteBothPlus c p))

natEqRefl : {n : Nat} -> (n == n) = True
natEqRefl {n=Z} = Refl
natEqRefl {n=S n'} = natEqRefl {n=n'}




natGteEq : {a, b : Nat} ->
           (e1 : gte a b = True) ->
           (e2 : gte b a = True) ->
           (a == b) = True
natGteEq {a=Z} {b=Z} e1 e2 = Refl
natGteEq {a=S a'} {b=Z} e1 e2 = e2
natGteEq {a=Z} {b=S b'} e1 e2 = e1
natGteEq {a=S a'} {b=S b'} e1 e2 = natGteEq {a=a'} {b=b'} e1 e2


natEqComm : {n1, n2 : Nat} ->
            (n1 == n2 = True) ->
            (n2 == n1) = True
natEqComm {n1=Z} {n2=Z} e = Refl
natEqComm {n1=Z} {n2=S _} e = e
natEqComm {n1=S _} {n2=Z} e = e
natEqComm {n1=S x} {n2=S y} e = natEqComm {n1=x} {n2=y} e


natEqTrans : {a, b, c : Nat} ->
             (a==b) = True ->
             (b==c) = True ->
             (a==c) = True
natEqTrans {a=Z} {b=Z} {c=Z} e1 e2 = Refl
natEqTrans {a=S a'} {b=Z} {c=Z} e1 e2 = e1
natEqTrans {a=Z} {b=S b'} {c=Z} e1 e2 = Refl
natEqTrans {a=Z} {b=Z} {c=S c'} e1 e2 = e2
natEqTrans {a=S a'} {b=S b'} {c=Z} e1 e2 = e2
natEqTrans {a=S a'} {b=Z} {c=S c'} e1 e2 = absurd $ trueNotFalse (sym e1)
natEqTrans {a=Z} {b=S b'} {c=S c'} e1 e2 = e1
natEqTrans {a=S a'} {b=S b'} {c=S c'} e1 e2 = natEqTrans {a=a'} {b=b'} {c=c'} e1 e2


lte_succLeft : (a, b, c : Nat) ->
               lte b (plus c a) = True ->
               lte b (S (plus c a)) = True
lte_succLeft Z Z Z e = Refl
lte_succLeft (S a) Z Z e = Refl
lte_succLeft Z (S b) Z e = absurd $ trueNotFalse (sym e)
lte_succLeft (S a) (S b) Z e = lte_succLeft a b Z e
lte_succLeft (S a) Z (S c) e = Refl
lte_succLeft Z (S b) (S c) e = lte_succLeft Z b c e
lte_succLeft Z Z (S c) e = Refl
lte_succLeft (S a) (S b) (S c) e = lte_succLeft (S a) b c e


natGtePlus : {a, b : Nat} ->
             (c : Nat) ->
             gte a b = True ->
             gte (plus c a) b = True
natGtePlus Z e {a} = e
natGtePlus (S c') e {a} {b} = lte_succLeft a b c' $ natGtePlus c' e


natRefl : (a, b : Nat) ->
            (a == b) = True ->
            a = b
natRefl Z Z e = Refl
natRefl (S a) Z e = absurd $ trueNotFalse (sym e)
natRefl Z (S b) e = absurd $ trueNotFalse (sym e)
natRefl (S a) (S b) e = cong $ natRefl a b e


natGtePlusEq : {n1, n2, n3 : Nat} ->
               (np : Nat) ->
               (b : Bool) ->
               gte (plus np n2) n1 = b ->
               (n2 == n3) = True ->
               gte (plus np n3) n1 = b
natGtePlusEq {n2} {n3} np b ge e = rewrite (sym $ natRefl n2 n3 e) in ge

natGteEqTrans : {a, b, c : Nat} ->
                (a == b) = True ->
                (bl : Bool) ->
                (gte b c = bl) ->
                gte a c = bl
natGteEqTrans {a} {b} e bl ge = rewrite (natRefl a b e) in ge

{-
natGtePlusF : (a, b : Nat) ->
              gte a (plus b a) = False
natGtePlusF Z Z = ?l
natGtePlusF (S a) Z = ?nn
natGtePlusF Z (S b) = ?nnb
natGtePlusF (S a) (S b) = ?mmml
-}


natOps : WeightOps Nat
natOps = MKWeight Z gte (==) plus
                  natEqRefl natEqComm natEqTrans
                  natGteEq nat_gteRefl nat_gte_reverse nat_gte_comm
                  nat_gteBothPlus natGtePlus natGtePlusEq
                  nat_tri natGteEqTrans plusCommutative


eg : Graph 4 Nat Graph.natOps
eg = MKGraph 4 Nat natOps (set0 :: set1 :: set2 :: set3 :: Nil)

nadj1 : inNodeset Graph.n0 Graph.set0 = False
nadj1 = Refl

--nadj_eg : (n : Node 4) -> inNodeset n (getNeighbors Graph.eg n) = False



eg' : Graph 4 Nat Graph.natOps
eg' = MKGraph 4 Nat natOps (set0' :: set1' :: set2' :: set3' :: Nil)

{-
p102 : Path Graph.n1 Graph.n2 Nat Graph.eg
p102 = Cons (Cons (Unit eg n1) eg n0 Refl) eg n2 Refl


p12 : Path Graph.n1 Graph.n2 Nat Graph.eg
p12 = Cons (Unit eg n1) eg n2 Refl
-}


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
