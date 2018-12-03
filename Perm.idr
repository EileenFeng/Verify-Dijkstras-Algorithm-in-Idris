module Perm
import CNat
import Logics
import Data.Vect

%default total

{--------------------------- Properties of `gt` ---------------------------}
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

{- `gt` is transitive -}
gt_trans : (x, y, z : Nat) -> (gt x y) = True -> (gt y z) = True -> (gt x z) = True
gt_trans (S x') (S y') Z _ _ = Refl
gt_trans (S x') (S y') (S z') r1 r2 = gt_trans x' y' z' r1 r2
gt_trans (S x') Z _ _ Refl impossible
gt_trans Z _ _ Refl _ impossible

{-   (x > z = True) -> (y > z = False) -> (x > y = True)   -}
gt_deduce : (x, y, z : Nat) -> (gt x z) = True -> (gt y z) = False -> (gt x y) = True
gt_deduce (S x') Z (S z') _ _ = Refl
gt_deduce (S x') Z Z Refl Refl = Refl
gt_deduce (S x') (S y') Z r1 Refl impossible
gt_deduce (S x') (S y') (S z') r1 r2 = gt_deduce x' y' z' r1 r2
gt_deduce Z _ _ Refl _ impossible 


{-   (a > b = True) -> (b > a = False)   -}
gt_imply : (a, b : Nat) -> (gt a b) = True -> (gt b a) = False
gt_imply (S a') Z _ = Refl
gt_imply (S a') (S b') r1 = gt_imply a' b' r1
gt_imply Z _ Refl impossible


gt_must_eq : (a, b : Nat) -> (gt a b) = False -> (gt b a) = False -> a = b
gt_must_eq Z Z r1 r2 = Refl
gt_must_eq Z (S b') _ Refl impossible
gt_must_eq (S k) Z Refl _ impossible
gt_must_eq (S a') (S b') r1 r2 = rewrite (gt_must_eq a' b' r1 r2) in Refl

onlyTrueOrFalse : (P : Bool) -> (P = True) -> (P = False) -> Void
onlyTrueOrFalse True Refl Refl impossible
onlyTrueOrFalse False Refl _ impossible



{--------------------------- Sorting a Vect ---------------------------}
insert : Nat -> Vect m Nat -> Vect (S m) Nat
insert n Nil = n :: Nil
insert n v@(x :: xs)
  = case (gt n x) of True  => x :: (insert n xs)
                     False => n :: v

vect_ins_sort : Vect n1 Nat -> Vect n1 Nat
vect_ins_sort Nil = Nil
vect_ins_sort (x' :: xs') = insert x' $ vect_ins_sort xs'


vect_ins_nil : (v : Vect Z Nat) -> vect_ins_sort v = Nil
vect_ins_nil Nil = Refl


vect_cons_eq : (a : Nat) -> (l, l' : Vect n Nat) -> l = l' -> a :: l = a :: l'
vect_cons_eq _ Nil Nil _ = Refl
vect_cons_eq _ (x :: xs) _ refl = rewrite refl in Refl

-- pattern match on ys
insert_elem_tail : Elem x ys -> Elem x (insert a ys)
insert_elem_tail {x} {a} Here with (gt a x) 
  | True = Here
  | False = There Here
insert_elem_tail {a} {ys=y::xs} (There e) with (gt a y)
  | True = There $ insert_elem_tail e 
  | False = There $ There e
  
{-
insert_elem_tail2 : Elem x ys -> Elem x (insert a ys)
insert_elem_tail2 {ys=Nil} elem = absurd $ noEmptyElem elem
insert_elem_tail2 {a} {ys=y::xs} elem with (gt a y) 
  | True = There $ insert_elem_tail2 
  | False = There elem 
-}

insert_elem_head : Elem x (insert x l')
insert_elem_head {l'=Nil} = Here
insert_elem_head {x} {l'=y :: ys} with (gt x y) 
  | True = There insert_elem_head 
  | False = Here


vect_ins_elem : Elem x al -> Elem x (vect_ins_sort al)
vect_ins_elem Here = insert_elem_head
vect_ins_elem (There e) = insert_elem_tail $ vect_ins_elem e


vect_ins_elem_inv : Elem x (vect_ins_sort al) -> Elem x al
vect_ins_elem_inv {al=Nil} e = absurd $ noEmptyElem e
vect_ins_elem_inv {al=a::as} e = ?hh


insert_reduce : insert a (vect_ins_sort l1) = insert a (vect_ins_sort l2) -> 
                vect_ins_sort l1 = vect_ins_sort l2
insert_reduce {l1 = Nil} {l2} _ = rewrite (vect_ins_nil l2) in Refl
insert_reduce {l1 = x1 :: l1'} {l2 = x2 :: l2'} refl  = ?insert_reduce_rhs_1

{-
  rewrite does not work with case statements: https://github.com/idris-lang/Idris-dev/issues/4001 
-}


insert_commutes : (insert a $ insert b l = insert b $ insert a l)
insert_commutes {l = Nil} {a} {b} with (gt a b) proof gt_a_b
  | True with (gt b a) proof gt_b_a
    | True = absurd (gt_anti_sym1 _ _ (sym gt_a_b) (sym gt_b_a)) -- ?tthole  -- True impossible
    | False = Refl
  | False with (gt b a) proof gt_b_a
    | True  = Refl
    | False = rewrite (gt_must_eq a b (sym gt_a_b) (sym gt_b_a)) in Refl
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
        | False = rewrite (gt_must_eq a b (sym gt_a_b) (sym gt_b_a)) in Refl



{---------------------------- permutations -------------------------------}

permutation : Vect n Nat -> Vect n Nat -> Type
permutation v1 v2 = (vect_ins_sort v1 = vect_ins_sort v2)


perm_skip : (x : Nat) ->
            permutation v1 v2 ->
            permutation (x :: v1) (x :: v2)
perm_skip _ refl = rewrite refl in Refl


perm_skip_reverse : permutation (x :: v1) (x :: v2) -> permutation v1 v2
perm_skip_reverse p = insert_reduce p


perm_swap : (x, y: Nat) ->
            (permutation (x :: y :: l) (y :: x :: l))
perm_swap x y {l} = insert_commutes {l= vect_ins_sort l} {a=x} {b=y}


perm_trans : (permutation l1 l2) -> (permutation l2 l3) -> (permutation l1 l3)
perm_trans p12 p23 = rewrite p12 in (rewrite p23 in Refl)

{-perm_trans _ _ {l1=Nil} {l3=Nil} = Refl
perm_trans _ _ {l1 = x :: xs} {l2 = y :: ys} {l3 = z :: zs} 
  = ?ptrans
-}


{-
perm_reformat : (x, y : Nat) ->
                (xs, ys : Vect (S n) Nat) -> 
                (xy : Vect n Nat) ->  
                permutation (x :: xs) (y :: ys) -> 
                (xs = y :: xy) -> 
                (ys = x :: xy) -> 
                permutation (x :: y :: xy) (x :: y :: xy)
perm_reformat x y xs ys Nil p e1 e2 = ?hole
-}

{--------------------- Properties of Permutations ---------------------}

perm_refl : (l : Vect n Nat) -> permutation l l
perm_refl Nil = Refl
perm_refl (x :: xs) = Refl


vect_append : Vect m Nat -> Vect n Nat -> Vect (plus n m) Nat
vect_append l' l {m} {n} = rewrite (plusCommutative n m) in (l' ++ l)

perm_app_comm : (l : Vect n Nat) -> 
                       (l' : Vect m Nat) -> 
                       (permutation (l ++ l') (vect_append l' l))  
perm_app_comm Nil Nil = Refl
perm_app_comm Nil (x :: xs) = ?permutation_app_comm_rhs_1
perm_app_comm (x :: xs) _ = ?permutation_app_comm_rhs_2


{- insert sort elem proof above-}
perm_elem : permutation al bl -> (Elem x al) -> (Elem x bl)
perm_elem {al=Nil} _ e = absurd $ noEmptyElem e
perm_elem {al} {bl} perm e = vect_ins_elem_inv $ rewrite (sym perm) in vect_ins_elem e 


forall_elem : (p : a -> Type) -> (vec : Vect n a) -> Type 
forall_elem {a} p v = (x : a) -> (Elem x v) -> p x


data Forall : (p : a -> Type) -> (vec : Vect n a) -> Type where
  Forall_nil : Forall p Nil
  Forall_cons : (p x) -> Forall p xs -> Forall p (x :: xs)


{- write proof for the other version of `forall` on the forall_perm first, and then prove that that `forall` and the above `Forall` definition are bidirectional -}
{- theorem Forall_Perm -}
forall_perm : (p : Nat -> Type) -> 
              (permutation al bl) -> 
              (Forall p al) -> 
              (Forall p bl)
--forall_perm _ _ Forall_nil = Forall_nil













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
