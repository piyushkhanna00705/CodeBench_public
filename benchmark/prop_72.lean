import Mathlib
lemma prop_72 (i: Nat) (xs: List α) :
  (List.reverse (List.drop i xs) = List.take (List.length xs - i) (List.reverse xs)):= by sorry