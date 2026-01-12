(* Sorted list predicate *)
(* Checks if a list of integers is sorted in ascending order *)

type [@grind] ilist = Nil | Cons of int * ilist

let [@simp] [@grind] rec sorted (l : ilist) : bool = match l with
| Nil -> true
| Cons (x, xs) -> match xs with
  | Nil -> true
  | Cons (y, ys) -> (x <= y) && sorted xs
