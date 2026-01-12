(* List length function *)
(* Computes the length of an integer list *)

type [@grind] ilist = Nil | Cons of int * ilist

let [@simp] [@grind] rec len (l : ilist) : int =
match l with
| Nil -> 0
| Cons (x, xs) -> 1 + len xs
