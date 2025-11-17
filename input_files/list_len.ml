type ilist = Nil | Cons of int * int list

let[@reflect] rec len (l : ilist) (n : int) : bool =
  match l with
  | Nil -> n == 0
  | Cons (_, rest) -> len rest (n - 1)