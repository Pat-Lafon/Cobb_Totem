(* Even list predicate *)
(* Checks if all elements in a list are even numbers *)

type [@grind] ilist = Nil | Cons of { head : int; tail : ilist }

let [@simp] [@grind] rec len (l : ilist) : int =
  match l with
  | Nil -> 0
  | Cons { head = _; tail = xs } -> 1 + len xs

let [@grind] rec is_even (x : int) : bool =
  if x = 0 then true else
    if x = 1 then false else
      if x = (0-1) then false else
        if x > 1 then is_even (x - 2) else
          is_even (x + 2)

let [@grind] rec all_even (l : ilist) : bool =
  match l with
  | Nil -> true
  | Cons { head = x; tail = xs } ->
      if is_even x then all_even xs else false