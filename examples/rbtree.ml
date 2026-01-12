(* Red-Black Tree invariants *)
(* Defines the core invariants for red-black trees:
   - num_black: black height consistency
   - no_red_red: no consecutive red nodes
   - rb_root_color: check root color
   - rbtree_invariant: combined invariant
   - rbdepth: tree depth *)

type [@grind] rbtree = Rbtleaf | Rbtnode of bool * rbtree * int * rbtree

let [@simp] [@grind] rec num_black (t : rbtree) (h : int) : bool =
  match t with
  | Rbtleaf -> h = 0
  | Rbtnode (c, l, v, r) ->
      if c then num_black l (h - 1) && num_black r (h - 1)
      else num_black l h && num_black r h

let [@simp] [@grind] rec no_red_red (t : rbtree) : bool =
  match t with
  | Rbtleaf -> true
  | Rbtnode (c, l, v, r) ->
      if not c then no_red_red l && no_red_red r
      else
        match (l, r) with
        | Rbtnode (c', l1, v1, r1), Rbtnode (c'', l2, v2, r2) ->
            (not c') && (not c'') && no_red_red l && no_red_red r
        | Rbtnode (c', l1, v1, r1), Rbtleaf -> (not c') && no_red_red l
        | Rbtleaf, Rbtnode (c'', l2, v2, r2) -> (not c'') && no_red_red r
        | Rbtleaf, Rbtleaf -> true

let [@simp] [@grind] rec rb_root_color (t : rbtree) (c : bool) : bool =
  match t with Rbtleaf -> false | Rbtnode (c', l, v, r) -> c = c'

let [@simp] [@grind] rec rbtree_invariant (t : rbtree) (h : int) : bool =
  match t with
  | Rbtleaf -> h = 0
  | Rbtnode (c, l, v, r) ->
      if not c then rbtree_invariant l (h - 1) && rbtree_invariant r (h - 1)
      else
        ((not (rb_root_color l true)) && not (rb_root_color r true))
        && rbtree_invariant l h && rbtree_invariant r h

let [@simp] [@grind] rec rbdepth (t : rbtree) : int =
  match t with
  | Rbtleaf -> 0
  | Rbtnode (c, l, v, r) -> 1 + ite (rbdepth l > rbdepth r) (rbdepth l) (rbdepth r)
