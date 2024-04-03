import Mathlib
lemma prop_81 (n: Nat) (m: Nat) (xs: List α)  :
  (List.take n (List.drop m xs) = List.drop m (List.take (n + m) xs)):= by sorry