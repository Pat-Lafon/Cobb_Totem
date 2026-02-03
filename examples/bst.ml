(* Binary Search Tree invariants *)
(* Defines BST property using upper/lower bound predicates *)

type [@grind] tree = Leaf | Node of { value : int; left : tree; right : tree }

let [@simp] [@grind] rec lower_bound (t : tree) (x : int) : bool =
match t with
| Leaf -> true
| Node { value = y; left = l; right = r } -> x <= y && lower_bound l x && lower_bound r x

let [@simp] [@grind] rec upper_bound (t : tree) (x : int) : bool =
match t with
| Leaf -> true
| Node { value = y; left = l; right = r } -> y <= x && upper_bound l x && upper_bound r x

let [@simp] [@grind] rec bst (t : tree) : bool =
match t with
| Leaf -> true
| Node { value = x; left = l; right = r } -> bst l && bst r && upper_bound l x && lower_bound r x
