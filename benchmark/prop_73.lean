import Mathlib
lemma prop_73 (p: α → Bool) (xs: List α) :
  (List.reverse (List.filter p xs) = List.filter p (List.reverse xs)):= by sorry