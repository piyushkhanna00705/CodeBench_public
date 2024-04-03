import Mathlib
def last: List Nat → Nat
  | [] => 0
  | [x] => x
  | _x::xs => (last xs)

lemma prop_64 x xs :
  (last (xs ++ [x]) = x):= by sorry