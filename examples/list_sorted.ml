(* Sorted list predicate *)
(* Checks if a list of integers is sorted in ascending order *)

type [@grind] ilist = Nil | Cons of { head : int; tail : ilist }

let [@simp] [@grind] rec len (l : ilist) : int =
  match l with
  | Nil -> 0
  | Cons { head = _; tail = xs } -> 1 + len xs

let [@simp] [@grind] rec sorted (l : ilist) : bool = match l with
| Nil -> true
| Cons { head = x; tail = xs } -> match xs with
  | Nil -> true
  | Cons { head = y; tail = ys } -> (x <= y) && sorted xs
