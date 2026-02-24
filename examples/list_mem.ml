type [@grind] ilist = Nil | Cons of { head : int; tail : ilist }

let [@simp] [@grind] rec mem (l : ilist) (x : int) : bool =
  match l with
  | Nil -> false
  | Cons { head = h; tail = t } -> (h = x) || mem t x
