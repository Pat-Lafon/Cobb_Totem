(* Complete tree predicate *)
(* A tree is complete if all leaves are at the same depth *)

type [@grind] tree = Leaf | Node of int * tree * tree

let [@simp] [@grind] rec height (t : tree) : int = match t with
| Leaf -> 0
| Node (v, l, r) -> 1 + ite (height l > height r) (height l) (height r)

let [@simp] [@grind] rec complete (t : tree) : bool =
match t with
| Leaf -> true
| Node (x, l, r) -> complete l && complete r && height l = height r
