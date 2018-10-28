module CNat
-- Nat.compare in Coq

%access export

public export
data Comparison = Gt | Eq | Lt

infixl 6 =??
(=??) : Nat -> Nat -> Comparison
(=??) Z m = case m of
           Z => Eq
           _ => Lt
(=??) (S n) m = case m of
               Z => Gt                                                                       
               S m' => (=??) n m'

infixl 6 =?
(=?) : Nat -> Nat -> Bool
(=?) n m = case (n =?? m) of
       	   Eq => True
	   _ => False

infixl 6 <=?
(<=?) : Nat -> Nat -> Bool
(<=?) n m = case (n =?? m) of
      	    Gt => False
	    _ => True

infixl 6 >=?
(>=?) : Nat -> Nat -> Bool
(>=?) n m = m <=? n

infixl 6 <?
(<?) : Nat -> Nat -> Bool
(<?) n m = (S n) <=? m

infixl 6 >?
(>?) : Nat -> Nat -> Bool
(>?) n m = m <? n
