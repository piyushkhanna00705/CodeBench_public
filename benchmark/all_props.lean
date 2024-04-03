import Mathlib

inductive MyTree (α: Type) where
| leaf : MyTree α
| node : MyTree α → α → MyTree α  →  MyTree α

def ins: Nat → List Nat → List Nat
  | n, []  =>  [n]
  | n, x::xs => if (n < x) then n :: x :: xs else x :: (ins n xs)

def last: List Nat → Nat
  | [] => 0
  | [x] => x
  | _x::xs => (last xs)

def insort : Nat → List Nat → List Nat
  | n, [] => [n]
  | n, x::xs => if n <= x then n::x::xs else x::(insort n xs)

def sort : List Nat → List Nat
  | [] => []
  | x::xs => insort x (sort xs)

def sorted : List Nat → Bool
  | [] => True
  | [_x] => True
  | x::y::xs => and (x <= y) (sorted (y::xs))

def ins1 : Nat → List Nat → List Nat
  | n, [] => [n]
  | n, x::xs => if n == x then x::xs else x::(ins1 n xs)

def dropWhile : (α → Bool) → List α → List α
  | _, [] => []
  | p, x::xs => if p x then dropWhile p xs else x::xs

def takeWhile : (α → Bool) → List α → List α
  | _, [] => []
  | p, x::xs => if p x then x ::(takeWhile p xs) else []

def delete : Nat → List Nat → List Nat
  | _, [] => []
  | n, x::xs => if n == x then (delete n xs) else x::(delete n xs)

def zip' : List α → List β → List (α × β)
  | [], _ => []
  | _, [] => []
  | x::xs, y::ys => ⟨x, y⟩ :: zip' xs ys

def zipConcat : α → List α → List β → List (α × β)
  | _, _, [] => []
  | x, xs, y::ys => ⟨x, y⟩ :: zip' xs ys

def null : List α → Bool
  | [] => True
  | _ => False

def butlast : List α → List α
  | [] => []
  | [_x] => []
  | x::xs => x::(butlast xs)

def butlastConcat : List α → List α → List α
  | xs, [] => butlast xs
  | xs, ys => xs ++ butlast ys

def lastOfTwo : List Nat → List Nat → Nat
  | xs, [] => last xs
  | _, ys => last ys

def height' : MyTree α → Nat
  | .leaf => 0
  | .node l _x r => (max (height' l) (height' r)).succ

def mirror : MyTree α → MyTree α
  | MyTree.leaf => MyTree.leaf
  | MyTree.node l x r => MyTree.node r x l

lemma prop_01 (n: Nat) (xs: List α) :
 List.take n xs ++ List.drop n xs = xs:= by sorry
lemma prop_02 (n: Nat) (xs: List Nat) (ys: List Nat) :
 List.count n xs + List.count n ys = List.count n (xs ++ ys):= by sorry
lemma prop_03 (n: Nat) (xs: List Nat) (ys: List Nat) :
 List.count n xs <= List.count n (xs ++ ys):= by sorry
lemma prop_04 (n: Nat) (xs: List Nat) :
  (List.count n xs).succ = List.count n (n :: xs):= by sorry
lemma prop_05 (n: Nat) (x: Nat) (xs: List Nat) :
 (n = x) →  (List.count n xs).succ = List.count n (x :: xs):= by sorry
lemma prop_06 (n: Nat) (m: Nat) :
 (n - (n + m) = 0):= by sorry
lemma prop_07 (n: Nat) (m: Nat) :
 ((n + m) - n = m):= by sorry
lemma prop_08 (k:Nat) (m: Nat) (n: Nat) :
  ((k + m) - (k + n) = m - n):= by sorry
lemma prop_09 (i: Nat) (j: Nat) (k: Nat) :
  ((i - j) - k = i - (j + k)):= by sorry
lemma prop_10 (m: Nat) :
 (m - m = 0):= by sorry
lemma prop_11 (xs: List α) :
   (List.drop 0 xs = xs):= by sorry
lemma prop_12 (n: Nat) (f: α → α) (xs: List α) :
   (List.drop n (List.map f xs) = List.map f (List.drop n xs)):= by sorry
lemma prop_13 (n: Nat) (x: α) (xs: List α) :
 (List.drop n.succ (x :: xs) = List.drop n xs):= by sorry
lemma prop_14 (p: α → Bool) (xs: List α) (ys: List α) :
  (List.filter p (xs ++ ys) = (List.filter p xs) ++ (List.filter p ys)):= by sorry
lemma prop_15 (x: Nat) (xs: List Nat) :
  (List.length (ins x xs)) = (List.length xs).succ:= by sorry
lemma prop_16 (x: Nat) (xs: List Nat) :
 xs = [] →  last (x::xs) = x:= by sorry
lemma prop_17 (n: Nat) :
  n <= 0 ↔ n = 0:= by sorry
lemma prop_18 i (m: Nat) :
   i < (i + m).succ:= by sorry
lemma prop_19 (n: Nat) (xs: List Nat) :
 (List.length (List.drop n xs) = List.length xs - n):= by sorry
lemma prop_20 (xs: List Nat) :
  (List.length (sort xs) = List.length xs):= by sorry
lemma prop_21 (n: Nat) (m: Nat) :
  n <= (n + m):= by sorry
lemma prop_22 (a: Nat) (b: Nat) (c: Nat) :
  (max (max a b) c = max a (max b c)):= by sorry
lemma prop_23 (a: Nat) (b: Nat) :
  (max a b = max b a):= by sorry
lemma prop_24 (a: Nat) (b: Nat) :
 (((max a b) = a) ↔ b <= a):= by sorry
lemma prop_25 (a: Nat) (b: Nat) :
  (((max a b) = b) ↔ a <= b):= by sorry
lemma prop_26 (x: α) (xs: List α) (ys: List α) :
  x ∈ xs →  x ∈ (xs ++ ys):= by sorry
lemma prop_27 (x: α) (xs: List α) (ys: List α) :
 x ∈ ys → x ∈ (xs ++ ys):= by sorry
lemma prop_28 (x: α) (xs: List α) :
  x ∈ (xs ++ [x]):= by sorry
lemma prop_29 (x: Nat) (xs: List Nat) :
  x ∈ ins1 x xs:= by sorry
lemma prop_30 (x: Nat) (xs: List Nat) :
  x ∈ ins x xs:= by sorry
lemma prop_31 (a: Nat) (b: Nat) (c: Nat) :
  min (min a b) c = min a (min b c):= by sorry
lemma prop_32 (a: Nat) (b: Nat) :
  min a b = min b a:= by sorry
lemma prop_33 (a: Nat) (b: Nat) :
  min a b = a ↔ a <= b:= by sorry
lemma prop_34 (a: Nat) (b: Nat) :
  min a b = b ↔ b <= a:= by sorry
lemma prop_35 (xs: List α) :
  dropWhile (fun _ => False) xs = xs:= by sorry
lemma prop_36 (xs: List α) :
  takeWhile (fun _ => True) xs = xs:= by sorry
lemma prop_37 (x: Nat) (xs: List Nat) :
  not (x ∈ delete x xs):= by sorry
lemma prop_38 (n: Nat) (xs: List Nat) :
  List.count n (xs ++ [n]) = (List.count n xs).succ:= by sorry
lemma prop_39 (n: Nat) (x: Nat) (xs: List Nat) :
  List.count n [x] + List.count n xs = List.count n (x::xs):= by sorry
lemma prop_40 (xs: List α) :
 (List.take 0 xs = []):= by sorry
lemma prop_41 (n: Nat) (f: α → α) (xs: List α) :
  (List.take n (List.map f xs) = List.map f (List.take n xs)):= by sorry
lemma prop_42 (n: Nat) (x: α) (xs: List α) :
  (List.take n.succ (x::xs) = x :: (List.take n xs)):= by sorry
lemma prop_43 (p: Nat → Bool) (xs: List Nat) :
  (takeWhile p xs ++ dropWhile p xs = xs):= by sorry
lemma prop_44 (x: α) (xs: List α) (ys: List β) :
  zip' (x::xs) ys = zipConcat x xs ys:= by sorry
lemma prop_45 (x: α) (y: β) (xs: List α) (ys: List β) :
  zip' (x::xs) (y::ys) = (x, y) :: zip' xs ys:= by sorry
lemma prop_46 {α β: Type} (xs: List β) :
  zip' ([]: List α) xs = []:= by sorry
lemma prop_47 (a: MyTree α) :
  (height' (mirror a) = height' a):= by sorry
lemma prop_48 (xs: List Nat) :
  not (null xs) → butlast xs ++ [last xs] = xs:= by sorry
lemma prop_49 (xs: List Nat) (ys: List Nat) :
  (butlast (xs ++ ys) = butlastConcat xs ys):= by sorry
lemma prop_50 (xs: List α) :
  (butlast xs = List.take (List.length xs - 1) xs):= by sorry
lemma prop_51 (xs: List α) (x: α) :
  (butlast (xs ++ [x]) = xs):= by sorry
lemma prop_52 (n: Nat) xs :
  (List.count n xs = List.count n (List.reverse xs)):= by sorry
lemma prop_53 (n: Nat) xs :
  (List.count n xs = List.count n (sort xs)):= by sorry
lemma prop_54 (n: Nat) (m: Nat) :
  ((m + n) - n = m):= by sorry
lemma prop_55 (n: Nat) (xs: List α) (ys: List α) :
  (List.drop n (xs ++ ys) = List.drop n xs ++ List.drop (n - List.length xs) ys):= by sorry
lemma prop_56 (n: Nat) (m: Nat) (xs: List α) :
  (List.drop n (List.drop m xs) = List.drop (n + m) xs):= by sorry
lemma prop_57 (n: Nat) (m: Nat) (xs: List α) :
  (List.drop n (List.take m xs) = List.take (m - n) (List.drop n xs)):= by sorry
lemma prop_58 (n: Nat) (xs: List α) (ys: List β) :
  (List.drop n (zip' xs ys) =  zip' (List.drop n xs) (List.drop n ys)):= by sorry
lemma prop_59 (xs: List Nat) (ys: List Nat) :
  ys = [] →  last (xs ++ ys) = last xs:= by sorry
lemma prop_60 (xs: List Nat) (ys: List Nat) :
  not (null ys) → last (xs ++ ys) = last ys:= by sorry
lemma prop_61 (xs: List Nat) (ys: List Nat) :
  (last (xs ++ ys) = lastOfTwo xs ys):= by sorry
lemma prop_62 (xs: List Nat) (x: Nat) :
  not (null xs) → last (x::xs) = last xs:= by sorry
lemma prop_63 (n: Nat) (xs: List Nat) :
  n < List.length xs → last (List.drop n xs) = last xs:= by sorry
lemma prop_64 x xs :
  (last (xs ++ [x]) = x):= by sorry
lemma prop_65 (i: Nat) (m: Nat) :
  i < (m + i).succ:= by sorry
lemma prop_66 (p: α → Bool) (xs: List α) :
  List.length (List.filter p xs) <= List.length xs:= by sorry
lemma prop_67 (xs: List Nat) :
  List.length (butlast xs) = List.length xs - 1:= by sorry
lemma prop_68 (n: Nat) (xs: List Nat) :
  List.length (delete n xs) <= List.length xs:= by sorry
lemma prop_69 (n: Nat) (m: Nat) :
  n <= (m + n):= by sorry
lemma prop_70 m (n: Nat) :
  m <= n → m <= n.succ:= by sorry
lemma prop_71 (x:Nat) (y :Nat) (xs: List Nat) :
  (x == y) = False → ((x ∈ (ins y xs)) == (x ∈ xs)):= by sorry
lemma prop_72 (i: Nat) (xs: List α) :
  (List.reverse (List.drop i xs) = List.take (List.length xs - i) (List.reverse xs)):= by sorry
lemma prop_73 (p: α → Bool) (xs: List α) :
  (List.reverse (List.filter p xs) = List.filter p (List.reverse xs)):= by sorry
lemma prop_74 (i: Nat) (xs: List α) :
  (List.reverse (List.take i xs) = List.drop (List.length xs - i) (List.reverse xs)):= by sorry
lemma prop_75 (n: Nat) (m: Nat ) (xs: List Nat) :
  (List.count n xs + List.count n [m] = List.count n (m :: xs)):= by sorry
lemma prop_76 (n: Nat) (m: Nat) (xs: List Nat) :
  (n == m) = False → List.count n (xs ++ [m]) = List.count n xs:= by sorry
lemma prop_77 (x: Nat) (xs: List Nat) :
  sorted xs → sorted (insort x xs):= by sorry
lemma prop_78 (xs: List Nat) :
  sorted (sort xs):= by sorry
lemma prop_79 (m: Nat) (n: Nat) (k: Nat) :
  ((m.succ - n) - k.succ = (m - n) - k):= by sorry
lemma prop_80 (n: Nat) (xs: List α) (ys: List α) :
  (List.take n (xs ++ ys) = List.take n xs ++ List.take (n - List.length xs) ys):= by sorry
lemma prop_81 (n: Nat) (m: Nat) (xs: List α)  :
  (List.take n (List.drop m xs) = List.drop m (List.take (n + m) xs)):= by sorry
lemma prop_82 (n: Nat) (xs: List α) (ys: List β) :
  (List.take n (zip' xs ys) = zip' (List.take n xs) (List.take n ys)):= by sorry
lemma prop_83 (xs: List α) (ys: List α) (zs: List β) :
  (zip' (xs ++ ys) zs =
           zip' xs (List.take (List.length xs) zs) ++ zip' ys (List.drop (List.length xs) zs)):= by sorry
lemma prop_84 (xs: List α) (ys: List β) (zs: List β) :
  (zip' xs (ys ++ zs) =
           zip' (List.take (List.length ys) xs) ys ++ zip' (List.drop (List.length ys) xs) zs):= by sorry
lemma prop_85 (xs: List α) (ys: List β) :
  (List.length xs = List.length ys) →
    (zip' (List.reverse xs) (List.reverse ys) = List.reverse (zip' xs ys)):= by sorry
lemma prop_86 (x: Nat) (y: Nat) (xs: List Nat) :
  x < y → ((x ∈ (ins y xs)) == (x ∈ xs)):= by sorry
