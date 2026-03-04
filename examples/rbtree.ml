type [@grind] rbtree = Rbtleaf | Rbtnode of { color : bool; left : rbtree; value : int; right : rbtree }

let [@simp] [@grind] rec num_black (t : rbtree) (h : int) : bool =
  match t with
  | Rbtleaf -> h = 0
  | Rbtnode { color = c; left = l; value = _; right = r } ->
      if not c then num_black l (h - 1) && num_black r (h - 1)
      else num_black l h && num_black r h

let [@simp] [@grind] rec no_red_red (t : rbtree) : bool =
  match t with
  | Rbtleaf -> true
  | Rbtnode { color = c; left = l; value = _; right = r } ->
      if c then no_red_red l && no_red_red r
      else
        match l with
        | Rbtnode { color = c'; left = _; value = _; right = _ } ->
            (match r with
            | Rbtnode { color = c''; left = _; value = _; right = _ } ->
                c' && c'' && no_red_red l && no_red_red r
            | Rbtleaf -> c' && no_red_red l)
        | Rbtleaf ->
            (match r with
            | Rbtnode { color = c''; left = _; value = _; right = _ } -> c'' && no_red_red r
            | Rbtleaf -> true)

let [@simp] [@grind] rb_root_color (t : rbtree) (c : bool) : bool =
  match t with Rbtleaf -> false | Rbtnode { color = c'; left = _; value = _; right = _ } -> c = c'

let [@simp] [@grind] rbtree_invariant (t : rbtree) (h : int) : bool =
  no_red_red t && num_black t h && rb_root_color t false