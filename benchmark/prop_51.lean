import Mathlib
def butlast : List α → List α
  | [] => []
  | [_x] => []
  | x::xs => x::(butlast xs)

lemma prop_51 (xs: List α) (x: α) :
  (butlast (xs ++ [x]) = xs):= by sorry