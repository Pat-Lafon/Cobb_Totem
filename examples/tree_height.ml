(* Tree height function *)
(* Computes the height of a binary tree *)

type [@grind] tree = Leaf | Node of { value : int; left : tree; right : tree }

let [@simp] [@grind] rec height (t : tree) : int = match t with
| Leaf -> 0
| Node { value = v; left = l; right = r } -> ite (height l > height r) (1 + height l) (1 + height r)
