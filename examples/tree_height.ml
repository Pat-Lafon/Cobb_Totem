(* Tree height function *)
(* Computes the height of a binary tree *)

type [@grind] tree = Leaf | Node of int * tree * tree

let [@simp] [@grind] rec height (t : tree) : int = match t with
| Leaf -> 0
| Node (v, l, r) -> 1 + ite (height l > height r) (height l) (height r)
