module CNat
-- Nat.compare in Coq

%access export

public export

data Comparison = Gt | Eq | Lt

data Smaller : a -> Bool -> Type where
  SmallerT : prop -> Smaller prop True
  SmallerF : prop -> Smaller prop False

infix 6 =??
(=??) : Nat -> Nat -> Comparison
(=??) Z m = case m of
           Z => Eq
           _ => Lt
(=??) (S n) m = case m of
               Z => Gt                                                                       
               S m' => (=??) n m'
{-
infix 6 =?
(=?) : Nat -> Nat -> Bool
Z =? Z           = True
(S n) =? (S m)   = n =? m
_ =? _ = False
-}

infix 6 <=?
(<=?) : Nat -> Nat -> Bool
Z <=? _ = True
_ <=? Z = False
(S n) <=? (S m) = n <=? m

infix 6 >=?
(>=?) : Nat -> Nat -> Bool
(>=?) n m = m <=? n

infix 6 <?
(<?) : Nat -> Nat -> Bool
(<?) n m = (S n) <=? m

infix 6 >?
(>?) : Nat -> Nat -> Bool
(>?) n m = m <? n
