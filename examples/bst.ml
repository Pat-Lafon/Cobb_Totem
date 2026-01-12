(* Binary Search Tree invariants *)
(* Defines BST property using upper/lower bound predicates *)

type [@grind] tree = Leaf | Node of int * tree * tree

let [@simp] [@grind] rec lower_bound (t : tree) (x : int) : bool =
match t with
| Leaf -> true
| Node (y, l, r) -> x <= y && lower_bound l x && lower_bound r x

let [@simp] [@grind] rec upper_bound (t : tree) (x : int) : bool =
match t with
| Leaf -> true
| Node (y, l, r) -> y <= x && upper_bound l x && upper_bound r x

let [@simp] [@grind] rec bst (t : tree) : bool =
match t with
| Leaf -> true
| Node (x, l, r) -> bst l && bst r && upper_bound l x && lower_bound r x
