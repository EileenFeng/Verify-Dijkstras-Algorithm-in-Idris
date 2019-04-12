module Example
import Data.Vect

%default total
-- examples for background
CharList : Type
CharList = List Char


lisChar : CharList 
lisChar = 'h' :: 'e' :: 'l' :: 'l' :: 'o' :: Nil


concat : Vect n Nat -> Vect m Nat -> Vect (plus n m) Nat
concat Nil v2 = v2
concat (x :: xs) ys = x :: (concat xs ys)


reverse : (elem : Type) -> List elem -> List elem

nats : List Nat
nats = 3 :: 2 :: 1 :: Nil
  
reverse_nats : List Nat
reverse_nats = reverse Nat nats


findNat : Nat -> Vect m Nat -> Bool
findNat _ Nil = False
findNat n (x :: xs) = case (n == x) of 
                           True => True
                           False => findNat n xs
                           
                           
checkEven : Nat -> Bool
checkEven Z = True
checkEven (S n) = case (checkEven n) of 
                       True => False
                       False => True


checkEvenPrf : (n : Nat) -> 
               (checkEven n = True) -> 
               checkEven (S n) = False
checkEvenPrf n prf with (checkEven n) proof nIsEven
  | True = Refl
  | False = absurd $ trueNotFalse (sym prf)
  

predN : Nat -> Nat
predN Z = Z
predN (S n) = n

checkEven_wrong : (n : Nat) -> 
                  (checkEven n = True) -> 
                  checkEven (predN n) = False
checkEven_wrong Z prf = ?caseZ   
checkEven_wrong (S pn) prf with (checkEven pn) proof pnIsEven
  | True = absurd $ trueNotFalse (sym prf)
  | False = Refl
  
{-
wrong_concat : Vect n Nat -> Vect m Nat -> Vect (n+m) Nat
wrong_concat Nil v2 = v2
wrong_concat (x :: xs) ys = wrong_concat (x :: xs) ys
-}

