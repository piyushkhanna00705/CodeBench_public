import Mathlib

inductive MyTree (α: Type) where
| leaf : MyTree α
| node : MyTree α → α → MyTree α  →  MyTree α

def height' : MyTree α → ℕ
  | .leaf => 0
  | .node l _x r => (max (height' l) (height' r)).succ

def mirror : MyTree α → MyTree α
  | MyTree.leaf => MyTree.leaf
  | MyTree.node l x r => MyTree.node r x l

lemma prop_47 (a: MyTree α) :
  (height' (mirror a) = height' a):= by sorry
