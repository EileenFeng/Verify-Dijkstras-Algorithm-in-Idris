module Logics
import CNat
import Decidable.Equality
%default total

%access public export

infixl 7 /\
data (/\) : a -> b -> Type where
     Conj : a -> b -> (a /\ b)

infixl 6 <->
data (<->) : a -> b -> Type where
     Iff : (a -> b) -> (b -> a) -> (a <-> b)

-- plus_comm from http://docs.idris-lang.org/en/latest/proofs/patterns.html
plus_commutes_Z : m = plus m 0
plus_commutes_Z {m = Z} = Refl
plus_commutes_Z {m = (S k)} = let rec = plus_commutes_Z {m=k} in
                                  rewrite rec in Refl

plus_commutes_S : (k : Nat) -> (m : Nat) -> S (plus m k) = plus m (S k)
plus_commutes_S k Z = Refl
plus_commutes_S k (S j) = rewrite plus_commutes_S k j in Refl

data PReflect : a -> Bool -> Type
  where ReflectT : prop -> PReflect prop True
        ReflectF : Not prop -> PReflect prop False


iff_reflect : (prop <-> (bool=True)) -> PReflect prop bool
iff_reflect {bool} (Iff pTob bToP)
  = case bool of
    	 True => ReflectT (bToP Refl)
	 False => ReflectF (\p => case (pTob p) of
	       	       Refl impossible)


iff_comm : (prop1 <-> prop2) -> (prop2 <-> prop1)
iff_comm (Iff p1 p2) = Iff p2 p1

-- induction on Nats, reference to http://docs.idris-lang.org/en/latest/proofs/inductive.html
nat_induction : (P : Nat -> Type) ->
	      	(P Z) ->
	      	((n : Nat) -> P n -> P (S n)) ->
		(x : Nat) -> P x
nat_induction _ pZ _ Z = pZ
nat_induction _ pZ ps (S n) = ps _ (nat_induction _ pZ ps n)

{- Properties for `=?` -}
beq_nat_reflex : (n : Nat) -> ((n =? n) = True)
beq_nat_reflex Z = Refl
beq_nat_reflex (S n') = let rec = beq_nat_reflex n' in
                            rewrite rec in Refl

beq_nat_comm : (n : Nat) ->
               (m : Nat) ->
               ((n =? m) = True) ->
               ((m =? n) = True)
beq_nat_comm n = nat_induction prop h1 h2 n
  where
    prop : Nat -> Type
    prop = \n1 => (m : Nat) -> ((n1 =? m) = True) -> ((m =? n1) = True)

    h1 : (m : Nat) -> ((0 =? m) = True) -> ((m =? 0) = True)
    h1 Z _ = Refl
    h1 (S m') Refl impossible

    h2 : (n1 : Nat) ->
         ((m : Nat) -> ((n1 =? m) = True) -> ((m =? n1) = True)) ->
         (m : Nat) -> ((S n1 =? m) = True) -> ((m =? S n1) = True)
    h2 n1 ih Z Refl impossible
    h2 n1 ih (S m') refl = ih m' refl


-- proof for `beq_nat_true_iff` (Nat.eqb_eq)
beq_nat_true_1 : (n : Nat) ->
                 (m : Nat) ->
                 (n = m) ->
                 ((n =? m)=True)
beq_nat_true_1 n = nat_induction prop h1 h2 n
  where
    prop : Nat -> Type
    prop = \n1 => (m : Nat) -> (n1 = m) -> ((n1 =? m) = True)

    h1 : (m : Nat) -> (0 = m) -> ((0 =? m) = True)
    h1 Z _  = Refl
    h1 (S m') Refl impossible

    h2 : (n1 : Nat)
      -> ((m : Nat) -> (n1 = m) -> ((n1 =? m) = True))
      -> (m : Nat) -> (S n1 = m) -> ((S n1 =? m) = True)
    h2 _ ih Z Refl impossible
    h2 _ ih (S m') Refl  = ih m' Refl


beq_nat_true_2 : (n : Nat) ->
                 (m : Nat) ->
                 ((n =? m)=True) ->
                 (n = m)
beq_nat_true_2 n = nat_induction prop h1 h2 n
  where
    prop : Nat -> Type
    prop = \n1 => (m : Nat) -> ((n1 =? m) = True) -> (n1 = m)

    h1 : (m : Nat) -> ((0 =? m) = True) -> (0 = m)
    h1 Z _ = Refl
    h1 (S m') Refl impossible

    h2 : (n1 : Nat)
      -> ((m : Nat) -> ((n1 =? m) = True) -> (n1 = m))
      -> (m : Nat) -> ((S n1 =? m) = True) -> (S n1 = m)
    h2 n1 ih Z Refl impossible
    h2 n1 ih (S m') refl = let rec = ih m' refl in
                               rewrite rec in Refl

beq_nat_true_iff : (n = m) <-> ((n =? m) = True)
beq_nat_true_iff {n} {m} = Iff (beq_nat_true_1 n m) (beq_nat_true_2 n m)

beq_reflect : PReflect (x = y) (x =? y)
beq_reflect {x} {y} = iff_reflect $ beq_nat_true_iff {n = x} {m = y}

{-
-- Proof for blt_reflect

ltb_lt_1 : (n : Nat) -> (m : Nat) -> ((n <? m) = True) -> ((n < m) = True)
ltb_lt_1 n = nat_induction prop h1 h2 n
  where
    prop : Nat -> Type
    prop = \n1 => (m : Nat) -> ((n <? m) = True) -> (n < m)

    h1 : (m : Nat) -> ((0 <? m) = True) -> (n < m)
    h1 Z Refl impossible

    h2 : (n1 : Nat) ->
         ((m : Nat) -> ((n1 <? m) = True) -> (n1 < m)) ->
         (m : Nat) -> ((S n1 <? m) = True) -> (S n1 < m)

ltb_lt : ((n <? m) = True) <-> (n < m)

blt_reflect : PReflect (n < m) (n <? m)
blt_reflect = iff_reflect $ iff_comm ltb_lt
-}
