import Mathlib
def butlast : List α → List α
  | [] => []
  | [_x] => []
  | x::xs => x::(butlast xs)

lemma prop_67 (xs: List Nat) :
  List.length (butlast xs) = List.length xs - 1:= by sorry