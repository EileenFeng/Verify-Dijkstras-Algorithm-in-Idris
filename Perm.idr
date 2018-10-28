module Perm
import CNat
import Decidable.Equality
%default total 
-- reference for (->>) and (<->) : https://github.com/domdere/logic-idris

infixl 7 /\
data (/\) : a -> b -> Type where
     Conj : a -> b -> (a /\ b)

infixl 6 <->
data (<->) : a -> b -> Type where
     Iff : (a -> b) -> (b -> a) -> (a <-> b)

iff_mp1 : (a <-> b) -> a -> b
iff_mp1 (Iff a_to_b b_to_a) preda = a_to_b preda

iff_mp2 : (a <-> b) -> b -> a
iff_mp2 (Iff a_to_b b_to_a) predb = b_to_a predb

data PReflect : Type -> Bool -> Type
  where ReflectT : prop -> PReflect prop True
        ReflectF : Not prop -> PReflect prop False


iff_reflect : (prop <-> (bool=True)) -> PReflect prop bool
iff_reflect {bool} (Iff pTob bToP)
  = case bool of
    	 True => ReflectT (bToP Refl)
	 False => ReflectF (\p => case (pTob p) of
	       	       Refl impossible)
	 --ReflectF (\p => trueNotFalse $ sym (pTob p))

-- induction on Nats, reference to http://docs.idris-lang.org/en/latest/proofs/inductive.html 
nat_induction : (P : Nat -> Type) ->
	      	(P Z) -> 
	      	((k : Nat) -> P k -> P (S k)) ->
		(x : Nat) -> P x
nat_induction P pZ pk Z = pZ
nat_induction P pZ pk (S n) = pk n (nat_induction P pZ pk n)

-- extractFst $ the (1=1) Refl
extractFst : {x : ty} -> x = x -> ty
extractFst {x} Refl = x

-- equivalent to Nat.eqb_eq
beq_nat_true_1 : (n : Nat) -> (m : Nat) -> (n = m) -> ((n =? m)=True)
beq_nat_true_1 n = nat_induction prop h1 ?h2 n
	       where
		prop : Nat -> Type
		prop = m -> (n = m) -> ((n =? m) = True)
		h1 : (m : Nat) -> (0 = m) -> ((0 =? m) = True)
		h1 Z 	  _ = Refl
		h1 (S m') Refl impossible

beq_nat_true_2 : ((n =? m)=True) -> (n = m)
{-beq_nat_true_2 {n} {m} eq = case (decEq n m) of
	       	       	   	Yes prop => prop
				No contra => ?h
-}

beq_nat_true_iff : (n = m) <-> ((n =? m) = True)
beq_nat_true_iff = Iff beq_nat_true_1 beq_nat_true_2
		       	   
beq_reflect : PReflect (x = y) (x =? y)
beq_reflect {x} {y} = iff_reflect $ beq_nat_true_iff {n = x} {m = y}
				     
-- example from book
disjoint : (n : Nat) -> Z = S n -> Void
disjoint n p = replace {P = disjointTy} p ()
  where
    disjointTy : Nat -> Type
    disjointTy Z = ()
    disjointTy (S k) = Void

twoPlusTwo : 2 + 2 = 4
twoPlusTwo = Refl

imp0 : Nat -> Bool
imp0 Z = False
imp0 _ = True

imp1 : Bool -> Nat
imp1 False = Z
imp1 True = 3

iff : Nat <-> Bool
iff = Iff imp0 imp1

{-
	n + 0 = 0
	=? is reflexive, communicative
	associativity of plus
	communicative of plus
-}