(* Red-Black Tree invariants *)
(* Defines the core invariants for red-black trees:
   - num_black: black height consistency
   - no_red_red: no consecutive red nodes
   - rb_root_color: check root color
   - rbtree_invariant: combined invariant
   - rbdepth: tree depth *)

type [@grind] rbtree = Rbtleaf | Rbtnode of { color : bool; left : rbtree; value : int; right : rbtree }

let [@simp] [@grind] rec num_black (t : rbtree) (h : int) : bool =
  match t with
  | Rbtleaf -> h = 0
  | Rbtnode { color = c; left = l; value = v; right = r } ->
      if c then num_black l (h - 1) && num_black r (h - 1)
      else num_black l h && num_black r h

let [@simp] [@grind] rec no_red_red (t : rbtree) : bool =
  match t with
  | Rbtleaf -> true
  | Rbtnode { color = c; left = l; value = v; right = r } ->
      if not c then no_red_red l && no_red_red r
      else
        match l with
        | Rbtnode { color = c'; left = l1; value = v1; right = r1 } ->
            (match r with
            | Rbtnode { color = c''; left = l2; value = v2; right = r2 } ->
                (not c') && (not c'') && no_red_red l && no_red_red r
            | Rbtleaf -> (not c') && no_red_red l)
        | Rbtleaf ->
            (match r with
            | Rbtnode { color = c''; left = l2; value = v2; right = r2 } -> (not c'') && no_red_red r
            | Rbtleaf -> true)

let [@simp] [@grind] rec rb_root_color (t : rbtree) (c : bool) : bool =
  match t with Rbtleaf -> false | Rbtnode { color = c'; left = l; value = v; right = r } -> c = c'

let [@simp] [@grind] rec rbtree_invariant (t : rbtree) (h : int) : bool =
  match t with
  | Rbtleaf -> h = 0
  | Rbtnode { color = c; left = l; value = v; right = r } ->
      if not c then rbtree_invariant l (h - 1) && rbtree_invariant r (h - 1)
      else
        ((not (rb_root_color l true)) && not (rb_root_color r true))
        && rbtree_invariant l h && rbtree_invariant r h

let [@simp] [@grind] rec rbdepth (t : rbtree) : int =
  match t with
  | Rbtleaf -> 0
  | Rbtnode { color = c; left = l; value = v; right = r } -> if (rbdepth l > rbdepth r) then (1 + rbdepth l) else (1 + rbdepth r)
