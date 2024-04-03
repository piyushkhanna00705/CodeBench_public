import Mathlib
lemma prop_76 (n: Nat) (m: Nat) (xs: List Nat) :
  (n == m) = False → List.count n (xs ++ [m]) = List.count n xs:= by sorry