type [@grind] ilist = Nil | Cons of { head : int; tail : ilist }

let [@simp] [@grind] rec mem (x : int) (l : ilist) : bool =
  match l with
  | Nil -> false
  | Cons { head = h; tail = t } -> (h = x) || mem x t
