module Perm
import CNat
import Logics
import Data.Vect

%default total

{- Sorting a Vect -}
insert : Nat -> Vect m Nat -> Vect (S m) Nat
insert n Nil = n :: Nil
insert n v@(x :: xs)
  = case (gt n x) of True  => x :: (insert n xs)
                     False => n :: v

vect_ins_sort : Vect n1 Nat -> Vect n1 Nat
vect_ins_sort Nil = Nil
vect_ins_sort (x' :: xs') = insert x' $ vect_ins_sort xs'

gt_inv_t : (x, y : Nat) -> (gt (S x) (S y)) = True -> (gt x y) = True
gt_inv_t Z Z      Refl impossible
gt_inv_t Z (S _ ) Refl impossible
gt_inv_t (S _)  Z Refl = Refl
gt_inv_t (S x) (S y) r1 = r1

gt_inv_f : (x, y : Nat) -> (gt (S x) (S y)) = False -> (gt x y) = False
gt_inv_f Z Z Refl = Refl
gt_inv_f Z (S _) Refl = Refl
gt_inv_f (S _) Z Refl impossible
gt_inv_f (S x) (S y) r1 = r1

gt_anti_sym1 : (x, y : Nat) -> (gt x y) = True -> (gt y x) = True -> Void
gt_anti_sym1 Z Z Refl Refl impossible
gt_anti_sym1 (S x') Z Refl Refl impossible
gt_anti_sym1 Z (S y') Refl Refl impossible
gt_anti_sym1 (S x') (S y') r1 r2 = gt_anti_sym1 x' y' (gt_inv_t x' y' r1) (gt_inv_t y' x' r2)

gt_anti_sym2 : (x, y : Nat) -> (gt x y) = False -> (gt y x) = False -> Void
{-
gt_anti_sym2 (S x') Z Refl Refl impossible
gt_anti_sym2 Z (S y') Refl Refl impossible
gt_anti_sym2 (S x') (S y') r1 r2 = gt_anti_sym2 x' y' (gt_inv_f x' y' r1) (gt_inv_f y' x' r2)
-}

--vect_eq_impossible : (nil : Vect Z Nat) -> (x, y : Nat) -> ((x > y)=True) -> (x :: y :: nil) = (y :: x :: nil) -> Void


{- `gt` is transitive -}
gt_trans : (x, y, z : Nat) -> (gt x y) = True -> (gt y z) = True -> (gt x z) = True
gt_trans (S x') (S y') Z _ _ = Refl
gt_trans (S x') (S y') (S z') r1 r2 = gt_trans x' y' z' r1 r2
gt_trans (S x') Z _ _ Refl impossible
gt_trans Z _ _ Refl _ impossible

gt_deduce : (x, y, z : Nat) -> (gt x z) = True -> (gt y z) = False -> (gt x y) = True
gt_deduce (S x') Z (S z') _ _ = Refl
gt_deduce (S x') Z Z Refl Refl = Refl
gt_deduce (S x') (S y') Z r1 Refl impossible
gt_deduce (S x') (S y') (S z') r1 r2 = gt_deduce x' y' z' r1 r2
gt_deduce Z _ _ Refl _ impossible 


vect_cons_eq : (a : Nat) -> (l, l' : Vect n Nat) -> l = l' -> a :: l = a :: l'
vect_cons_eq _ Nil Nil _ = Refl
vect_cons_eq _ (x :: xs) _ refl = rewrite refl in Refl

{-
  rewrite does not work with case statements: https://github.com/idris-lang/Idris-dev/issues/4001 
-}

onlyTrueOrFalse : (P : Bool) -> (P = True) -> (P = False) -> Void
onlyTrueOrFalse True Refl Refl impossible
onlyTrueOrFalse False Refl _ impossible

gt_imply : (a, b : Nat) -> (gt a b) = True -> (gt b a) = False
gt_imply (S a') Z _ = Refl
gt_imply (S a') (S b') r1 = gt_imply a' b' r1
gt_imply Z _ Refl impossible


insert_commutes : (insert a $ insert b l = insert b $ insert a l)
insert_commutes {l = Nil} {a} {b} with (gt a b) proof gt_a_b
  | True with (gt b a) proof gt_b_a
    | True = absurd (gt_anti_sym1 _ _ (sym gt_a_b) (sym gt_b_a)) -- ?tthole  -- True impossible
    | False = Refl
  | False with (gt b a) proof gt_b_a
    | True  = Refl
    | False = ?ffhole  -- a == b
insert_commutes {l = (v :: vs)} {a} {b} with (gt a v) proof gt_a_v
  | True with (gt b v) proof gt_b_v
    | True with (gt a v)
      | True = vect_cons_eq v (insert a (insert b vs)) 
                              (insert b (insert a vs)) 
                              $ insert_commutes {l=vs} {a=a} {b=b}
      | False = absurd gt_a_v
    | False with (gt a b) proof gt_a_b
      | True with (gt a v) 
        | True = Refl
        | False = absurd gt_a_v
      | False = absurd $ onlyTrueOrFalse _ (gt_deduce a b v (sym gt_a_v) (sym gt_b_v)) (sym gt_a_b)
  | False with (gt b v) proof gt_b_v
    |True with (gt a v) proof gt_a_v2
      | True = absurd gt_a_v
      | False with (gt b a) proof gt_b_a
        | True with (gt b v) 
          | True = Refl
          | False = absurd gt_b_v
        | False = absurd $ onlyTrueOrFalse _ (gt_deduce b a v (sym gt_b_v) (sym gt_a_v2)) (sym gt_b_a)
    | False with (gt a b) proof gt_a_b
      | True with (gt a v) 
        | True = absurd $ gt_a_v
        | False with (gt b a) proof gt_b_a
          | True = absurd $ onlyTrueOrFalse _ (sym gt_a_b) (gt_imply b a (sym gt_b_a))
          | False = Refl
      | False with (gt b a) proof gt_b_a
        | True with (gt b v) 
          | True = absurd gt_b_v
          | False = Refl
        | False = ?ffff -- a == b?


{- permutations -}
permutation : Vect n Nat -> Vect n Nat -> Type
permutation v1 v2 = (vect_ins_sort v1 = vect_ins_sort v2)


perm_reduce : permutation (x :: xs) (y :: ys) -> (xy : Vect n Nat) -> permutation (x :: y :: xy) (x :: y :: xy)
perm_reduce {x} {y} _ Nil = Refl

perm_skip : (x : Nat) ->
            (permutation v1 v2) ->
            (permutation (x :: v1) (x :: v2))
perm_skip _ refl = rewrite refl in Refl


perm_swap : (x, y: Nat) ->
            (permutation (x :: y :: l) (y :: x :: l))
perm_swap x y {l} = insert_commutes {l= vect_ins_sort l} {a=x} {b=y}


perm_trans : (permutation l1 l2) -> (permutation l2 l3) -> (permutation l1 l3)
perm_trans _ _ {l1=Nil} {l3=Nil} = Refl
perm_trans _ _ {l1 = x :: xs} {l3 = z :: zs} = ?trans_rhs

{- properties of permutations-}
permutation_refl : (l : Vect n Nat) -> permutation l l
permutation_refl Nil = Refl
permutation_refl (x :: xs) = Refl


vect_append : Vect m Nat -> Vect n Nat -> Vect (plus n m) Nat
vect_append l' l {m} {n} = rewrite (plusCommutative n m) in (l' ++ l)


permutation_app_comm : (l : Vect n Nat) -> 
                       (l' : Vect m Nat) -> 
                       (permutation (l ++ l') (vect_append l' l))  
permutation_app_comm Nil Nil = Refl
permutation_app_comm Nil (x :: xs) = ?permutation_app_comm_rhs_1
permutation_app_comm (x :: xs) _ = ?permutation_app_comm_rhs_2


data Forall : (p : a -> Type) -> (vec : Vect n a) -> Type where
  Forall_nil : Forall p Nil
  Forall_cons : (p x) -> Forall p xs -> Forall p (x :: xs)

{- theorem Forall_Perm -}
forall_perm : (p : Nat -> Type) -> 
              (permutation al bl) -> 
              (Forall p al) -> 
              (Forall p bl)

{- Permutations -}
{-
data Permutation : (Vect n Nat) -> (Vect n Nat) -> Type where
  Perm_nil : Permutation Nil Nil
  Perm_refl : (vec : Vect n Nat) -> Permutation vec vec
  Perm_skip : (x : Nat) -> Permutation v1 v2 -> Permutation (x :: v1) (x :: v2)
  Perm_swap : (x : Nat) -> (y : Nat) -> (vec : Vect n Nat) -> Permutation (x :: y :: vec) (y :: x :: vec)
  Perm_trans : Permutation v1 v2 -> Permutation v2 v3 -> Permutation v1 v3
-}

-- {- permutations must equal after sorting -}
-- perm_equal : --(v1 : Vect n Nat) ->
--              --(v2 : Vect n Nat) ->
--              Permutation v1 v2 ->
--              (vect_ins_sort v1 = vect_ins_sort v2)
-- perm_equal Perm_nil      = Refl
-- perm_equal (Perm_refl _) = Refl
-- perm_equal (Perm_skip x perm) = ?pe_rhs2
-- perm_equal (Perm_swap x y vec) = ?pe_swap
-- {-
--   = case x < y of
--          True  => list_add_equal x $ list_add_equal y Refl
--          False => ?pe_2
-- -}
-- perm_equal (Perm_trans x y) = ?perm_equal_rhs_4
--
--
-- equal_perm : (v1 : Vect n Nat) ->
--              (v2 : Vect n Nat) ->
--              (vect_ins_sort v1 = vect_ins_sort v2) ->
--              Permutation v1 v2
--
-- {- two lists are permutations iff and only iff they are the same after sorting -}
-- iff_perm_equal : (perm : Permutation v1 v2) -> (perm <-> (vect_ins_sort v1 = vect_ins_sort v2))
-- iff_perm_equal perm {v1} {v2} = ?hole_iff--Iff (perm_equal perm) (equal_perm v1 v2)
--
--
-- -- Inverse cons for permutation
-- permutation_cons_inv : Permutation (a :: v1) (a :: v2) -> Permutation v1 v2
-- permutation_cons_inv Perm_nil impossible
-- permutation_cons_inv (Perm_refl (_ :: xs)) = Perm_refl xs
-- permutation_cons_inv (Perm_skip _ p) = p
-- permutation_cons_inv (Perm_swap x x vect) = Perm_skip x $ Perm_refl vect
-- permutation_cons_inv (Perm_trans p1 p2) = ?hole
--
--
-- vect_append : (v1 : Vect n Nat) -> (x : Nat) -> (v2 : Vect m Nat) -> Vect (S (plus n m)) Nat
-- vect_append v1 x v2 {n} {m} = rewrite (plus_commutes_S m n) in v1 ++ [x] ++ v2
--
-- -- Permutations eliminate same element should also results in permuation
-- permutation_elim_one : (x : Nat) ->
--                        (p1 : Vect (n + m) Nat) ->
--                        (p21 : Vect n Nat) ->
--                        (p22 : Vect m Nat) ->
--                        (Permutation (x :: p1) (vect_append p21 x p22)) ->
--                        (Permutation p1 (p21 ++ p22))
--
-- permutation_sym : Permutation v1 v2 -> Permutation v2 v1
--
-- {-
-- permutation_app_comm : (v1 : Vect n Nat) ->
--                        (v2 : Vect m Nat) ->
--                        Permutation (v1 ++ v2) (v2 ++ v1)
-- -}
-- -- some example for permutation
-- p1 : Permutation (3 :: 1 :: 2 :: Nil) (3 :: 2 :: 1 :: Nil)
-- p1 = Perm_skip 3 $ Perm_swap 1 2 Nil
--
-- p2 : Permutation (3 :: 2 :: 1 :: Nil) (2 :: 3 :: 1 :: Nil)
-- p2 = Perm_swap 3 2 $ (1 :: Nil)
--
-- p3 : Permutation (3 :: 1 :: 2 :: Nil) (2 :: 3 :: 1 :: Nil)
-- p3 = Perm_trans p1 p2
--
--
--
-- {-
-- permutation_cons_inv (Perm_swap x y p) impossible
-- permutation_cons_inv (Perm_swap x x p)  = Perm_skip x p
-- permutation_cons_inv (Perm_skip _ perm) = perm
-- permutation_cons_inv (Perm_trans (Perm_skip x p1) (Perm_skip x p2)) = Perm_trans p1 p2
-- permutation_cons_inv (Perm_trans (Perm_skip x p1) p2@(Perm_swap x x _))
--   = Perm_trans p1 $ permutation_cons_inv p2
-- permutation_cons_inv (Perm_trans (Perm_skip x p1) p2@(Perm_trans _ _))
--   = Perm_trans p1 $ permutation_cons_inv p2
-- permutation_cons_inv p@(Perm_trans p1@(Perm_swap x y p3) p2)
--   = ?hole1 --Perm_trans (permutation_cons_inv p1) (permutation_cons_inv p2)
-- permutation_cons_inv p@(Perm_trans p1@(Perm_trans x y) p2)
--   = ?hole2 --Perm_trans x $ Perm_trans y z
-- -}
--
-- -- vect_merge_sort : Vect n Nat -> Vect n Nat
-- -- vect_merge_sort Nil = Nil
-- -- vect_merge_sort v@(_ :: Nil) = v
-- -- vect_merge_sort vec = merge firstHalf secHalf
-- --   where
-- --     len : Nat
-- --     len = divNatNZ (length vec) 2 SIsNotZ
-- --     firstHalf : Vect len Nat
-- --     firstHalf = vect_merge_sort $ (fst $ splitAt len vec)
-- --     secHalf : Vect (length vec - len) Nat
-- --     secHalf = vect_merge_sort $ (snd $ splitAt len vec)
