(* Even list predicate *)
(* Checks if all elements in a list are even numbers *)

type [@grind] ilist = Nil | Cons of { head : int; tail : ilist }

let [@simp] [@grind] rec len (l : ilist) : int =
  match l with
  | Nil -> 0
  | Cons { head = _; tail = xs } -> 1 + len xs

let [@grind] is_even (x : int) : bool = (x mod 2 = 0)

let [@grind] rec all_even (l : ilist) : bool =
  match l with
  | Nil -> true
  | Cons { head = x; tail = xs } ->
      if is_even x then all_even xs else false