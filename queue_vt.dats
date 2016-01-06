staload "queue_vt.sats"

implement {a}
length(q) = 
  case+ q of
  | queue(h, t) => list_vt_length(h) + list_vt_length(t)

implement {a}
empty() = queue(list_vt_nil, list_vt_nil)

fun {a:vt@ype}
checkf
{lq, lhs, lts: addr}
{l, m: nat}
(
pf_hs: list_vt(a, l) @ lhs,
pf_ts: list_vt(a, m) @ lts |
q : queue_unfold(lq, lhs, lts),
p_hs: ptr lhs,
p_ts: ptr lts): queue_vt(a, l+m) = 
  case+ !p_hs of
  | ~list_vt_nil() => let
    val () = !p_hs := list_vt_reverse(!p_ts)
    val () = !p_ts := list_vt_nil
    prval () = fold@(q)
  in
    q
  end
  | list_vt_cons(_, _) => let
    prval () = fold@(q)
  in
    q
  end

implement {a}
push(xs, a) =
  case+ xs of
  | @queue(hs, ts) => let
    val () = ts := list_vt_cons(a, ts)
    prval pf_hs = view@hs
    prval pf_ts = view@ts
    val () = xs := checkf(pf_hs, pf_ts | xs, addr@hs, addr@ts)
  in
  end
  
implement {a}
pop(xs) =
  case+ xs of
  (* | @queue(h as ~list_vt_nil (), t) => let *)
  (*   val+ ~list_vt_cons(a, revt) = list_vt_reverse(t) *)
  (*   val () = h := revt *)
  (*   val () = t := list_vt_nil *)
  (*   prval () = fold@(xs) *)
  (* in *)
  (*   a *)
  (* end *)
  | @queue(hs as ~list_vt_cons(a, hs'), ts) => let
    val () = hs := hs'
    prval pf_hs = view@ hs
    prval pf_ts = view@ ts
    val () = xs := checkf(pf_hs, pf_ts | xs, addr@hs, addr@ts)
  in
    a
  end
