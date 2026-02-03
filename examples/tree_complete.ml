(* Complete tree predicate *)
(* A tree is complete if all leaves are at the same depth *)

type [@grind] tree = Leaf | Node of { value : int; left : tree; right : tree }

let [@simp] [@grind] rec height (t : tree) : int = match t with
| Leaf -> 0
| Node { value = v; left = l; right = r } -> ite (height l > height r) (1 + height l) (1 + height r)

let [@simp] [@grind] rec complete (t : tree) : bool =
match t with
| Leaf -> true
| Node { value = x; left = l; right = r } -> complete l && complete r && height l = height r
