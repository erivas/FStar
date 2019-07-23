module LowStar.Permissions

module F = FStar.FunctionalExtensionality
open FStar.Real

noeq type perms_rec' (a: Type0) = {
  current_max : perm_id;
  fully_owned: bool;
  perm_map    : F.restricted_t perm_id (fun (x:perm_id) -> permission & a)
}

let get_permission_from_pid' (#a: Type0) (p: perms_rec' a) (pid: perm_id) : GTot permission =
  let (perm, _) = p.perm_map pid in
  perm

let get_snapshot_from_pid' (#a: Type0) (p: perms_rec' a) (pid: perm_id) : Tot a =
  let (_, snap) = p.perm_map pid in snap

let is_live_pid' (#a: Type0) (v_perms: perms_rec' a) (pid:perm_id) : GTot bool =
  get_permission_from_pid' v_perms pid >. 0.0R

type live_pid' (#a: Type0) (v_perms: perms_rec' a) = pid:perm_id{is_live_pid' v_perms pid}

let is_fully_owned' (#a: Type0) (p: perms_rec' a) : GTot bool =
  p.fully_owned

let rec sum_until (#a: Type0) (f:perm_id -> permission & a) (n:nat) : GTot real =
  if n = 0 then 0.0R
  else
    let (x, _) = f n in x +. sum_until f (n - 1)

let perms_rec (a: Type0) = p:perms_rec' a{
  // Permissions are null above currently split objects
  (forall (n:perm_id). n > p.current_max ==> get_permission_from_pid' p n = 0.R) /\
  // The sum of permissions is the number of splits up till now
  (sum_until p.perm_map p.current_max = 1.0R)
}

[@inline_let]
let get_permission_from_pid = get_permission_from_pid'
[@inline_let]
let get_snapshot_from_pid = get_snapshot_from_pid'
[@inline_let]
let get_current_max #a p = p.current_max
[@inline_let]
let is_fully_owned = is_fully_owned'

let new_value_perms (#a: Type0) (init: a) (fully_owned: bool) =
  let f:F.restricted_t perm_id (fun (x:perm_id) -> permission & a) =
     F.on_dom perm_id (fun (x:perm_id) -> if x = 1 then
         ((FStar.Real.one <: permission), init)
       else
         (((FStar.Real.of_int 0) <: permission), init)
     )
  in
  ({ current_max = 1; perm_map = f; fully_owned = fully_owned }, 1)


let rec same_prefix_same_sum_until(#a: Type0) (p1 p2:perm_id -> permission & a) (n:nat) : Lemma
  (requires forall (x:perm_id). x <= n ==> begin
    let (perm1, _) = p1 x in let (perm2, _) = p2 x in
    perm1 = perm2
  end)
  (ensures sum_until p1 n = sum_until p2 n)
  = if n = 0 then () else same_prefix_same_sum_until p1 p2 (n-1)


let rec sum_until_change
  (#a: Type0)
  (p1 p2:perm_id -> permission & a)
  (n:nat)
  (i:perm_id)
  (v:permission)
  : Lemma (requires (forall (x:perm_id).
    let (v1, _) = p1 x in let (v2, _) = p2 x in
    (x <= n /\ x <> i) ==> v1 = v2) /\
    i <= n /\
    begin let (v', _) = p2 i in v' = v end
  ) (ensures (let (v', _) = p1 i in sum_until p2 n = sum_until p1 n +. v -. v'))
  =
    if n = i then same_prefix_same_sum_until p1 p2 (n-1)
    else sum_until_change p1 p2 (n-1) i v

let rec sum_until_extend_zeros
  (#a: Type0)
  (p:perm_id -> permission & a)
  (max:perm_id)
  (j:perm_id{j >= max})
  : Lemma
  (requires
    (forall (i:nat{i > max}). fst (p i) == 0.0R))
  (ensures sum_until p max == sum_until p j)
  =
    if j = max then ()
    else sum_until_extend_zeros p max (j-1)

let share_perms (#a: Type0) (#v: a) (v_perms: value_perms a v) (pid: live_pid v_perms)
  =
  let current_max' = v_perms.current_max + 1 in
  let (p, _) = v_perms.perm_map pid in
  let perm_map1' = F.on_dom perm_id (fun (x:perm_id) ->
    let (old_p, old_snap) = v_perms.perm_map x in
    if x = pid then ((p /. two <: permission), old_snap) else (old_p, old_snap))
  in
  sum_until_change v_perms.perm_map perm_map1' v_perms.current_max pid (p /. two);
  let perm_map2' = F.on_dom perm_id (fun (x:perm_id) ->
    let (old_p, old_snap) = perm_map1' x in
    if x = current_max' then ((p /. two <: permission), v) else (old_p, old_snap))
  in
  sum_until_change perm_map1' perm_map2' current_max' current_max' (p /. two);
  let v_perms' : perms_rec' a =
    { v_perms with
      current_max = current_max';
      perm_map = perm_map2'
    }
  in
  assert(forall (pid':perm_id{pid' <> current_max'}).
    is_live_pid' v_perms pid' <==>  is_live_pid' v_perms' pid'
  );
  assert(forall (pid':live_pid v_perms{pid' <> current_max'}).
    v == get_snapshot_from_pid v_perms pid'
  );
  assert(forall (pid':live_pid v_perms{pid' <> current_max'}).
    v == get_snapshot_from_pid' v_perms pid'
  );
  assert(forall (pid':live_pid' v_perms{pid' <> current_max'}).
     get_snapshot_from_pid' v_perms' pid' == get_snapshot_from_pid' v_perms pid'
  );
  assert(forall (pid':live_pid' v_perms'{pid' <> current_max'}).
    v == get_snapshot_from_pid' v_perms' pid'
  );
  (v_perms', current_max')

noextract
let share_perms_with_pid #a #v v_perms pid new_pid =
  let (p, _) = v_perms.perm_map pid in
  let perm_map1' = F.on_dom perm_id (fun (x:perm_id) ->
    let (old_p, old_snap) = v_perms.perm_map x in
    if x = pid then ((p /. two <: permission), old_snap) else (old_p, old_snap))
  in
  sum_until_change v_perms.perm_map perm_map1' v_perms.current_max pid (p /. two);
  let perm_map2' = F.on_dom perm_id (fun (x:perm_id) ->
    let (old_p, old_snap) = perm_map1' x in
    if x = new_pid then ((p /. two <: permission), v) else (old_p, old_snap))
  in
  sum_until_extend_zeros perm_map1' v_perms.current_max new_pid;
  sum_until_change perm_map1' perm_map2' new_pid new_pid (p /. two);
  let v_perms' : perms_rec' a =
    { v_perms with
      current_max = new_pid;
      perm_map = perm_map2'
    }
  in
  assert(forall (pid':perm_id{pid' <> new_pid}).
    is_live_pid' v_perms pid' <==>  is_live_pid' v_perms' pid'
  );
  assert(forall (pid':live_pid v_perms{pid' <> new_pid}).
    v == get_snapshot_from_pid v_perms pid'
  );
  assert(forall (pid':live_pid v_perms{pid' <> new_pid}).
    v == get_snapshot_from_pid' v_perms pid'
  );
  assert(forall (pid':live_pid' v_perms{pid' <> new_pid}).
     get_snapshot_from_pid' v_perms' pid' == get_snapshot_from_pid' v_perms pid'
  );
  assert(forall (pid':live_pid' v_perms'{pid' <> new_pid}).
    v == get_snapshot_from_pid' v_perms' pid'
  );
  v_perms'

private let rec sum_greater_than_subterm (#a: Type0) (f:perm_id -> permission & a) (n:nat) (pid1:perm_id)
  : Lemma (ensures (
    if n < pid1 then sum_until f n >=. 0.0R else
    sum_until f n >=. (let (x, _) = f pid1 in x)
  )) =
  if n = 0 then () else sum_greater_than_subterm f (n-1) pid1

private let rec sum_greater_than_subterms (#a: Type0) (f:perm_id -> permission & a) (n:nat) (pid1: perm_id)
  (pid2:perm_id{pid1 <> pid2})
  : Lemma (ensures (
    let (pid1, pid2) = if pid1 < pid2 then (pid1, pid2) else (pid2, pid1) in
    if n < pid1 then sum_until f n >=. 0.0R else
    if n < pid2 then sum_until f n >=. (let (x, _) = f pid1 in x) else
    sum_until f n >=. (let (x, _) = f pid1 in x) +. (let (x, _) = f pid2 in x)
  )) =
  if n = 0 then () else sum_greater_than_subterms f (n-1) pid1 pid2

let merge_perms
  (#a: Type0)
  (#v: a)
  (v_perms: value_perms a v)
  (pid1: live_pid v_perms)
  (pid2: live_pid v_perms{pid1 <> pid2})
  =
  let (p1, snap1) = v_perms.perm_map pid1 in
  let (p2, snap2) = v_perms.perm_map pid2 in
  sum_greater_than_subterms v_perms.perm_map v_perms.current_max pid1 pid2;
  let p_sum : permission = p1 +. p2 in
  let perm_map1' = F.on_dom perm_id (fun (x:perm_id) ->
    assert(sum_until v_perms.perm_map v_perms.current_max = 1.0R);
    if x = pid1 then ((p1 +. p2 <: permission), snap1)
    else v_perms.perm_map x
  ) in
  sum_until_change v_perms.perm_map perm_map1' v_perms.current_max pid1 p_sum;
  let perm_map2' = F.on_dom perm_id (fun (x:perm_id) ->
    if x = pid2 then ((0.0R <: permission), snap2) else perm_map1' x
  ) in
  sum_until_change perm_map1' perm_map2' v_perms.current_max pid2 0.0R;
  let v_perms': perms_rec' a =
    {  v_perms with perm_map = perm_map2' } in
  assert(forall (pid':perm_id{pid' <> pid2}).
    is_live_pid' v_perms pid' <==>  is_live_pid' v_perms' pid'
  );
  assert(forall (pid':live_pid' v_perms'{pid' <> pid2}).
    get_snapshot_from_pid' v_perms pid' == get_snapshot_from_pid' v_perms' pid'
  );
  assert(forall (pid': live_pid' v_perms').
      get_snapshot_from_pid v_perms pid' == get_snapshot_from_pid v_perms' pid'
  );
  v_perms'

let only_one_live_pid_with_full_permission'
  (#a: Type0)
  (v_perms: perms_rec a)
  (pid: perm_id)
  : Lemma (requires (get_permission_from_pid' v_perms pid == 1.0R))
    (ensures (forall (pid':live_pid' v_perms). pid == pid'))
  =
  let aux (pid': live_pid' v_perms) : Lemma (ensures (pid == pid')) =
    if pid <> pid' then
      sum_greater_than_subterms v_perms.perm_map v_perms.current_max pid pid'
    else
      ()
  in
  Classical.forall_intro aux

let only_one_live_pid_with_full_permission
  (#a: Type0)
  (#v: a)
  (v_perms: value_perms a v)
  (pid: perm_id)
  =
   let aux (pid': live_pid v_perms) : Lemma (ensures (pid == pid')) =
    if pid <> pid' then
      sum_greater_than_subterms v_perms.perm_map v_perms.current_max pid pid'
    else
      ()
  in
  Classical.forall_intro aux

let lemma_live_pid_smaller_max #a v_perms pid = ()

let lemma_greater_max_not_live_pid #a v_perms pid = ()

let change_snapshot
  (#a: Type0)
  (#v: a)
  (v_perms: value_perms a v)
  (pid: perm_id)
  (new_snapshot: a)
  =
  let v_perms' : perms_rec' a = { v_perms with
    perm_map = F.on_dom perm_id (fun (x:perm_id) ->
      if x = pid then
      let (p, _) = v_perms.perm_map x in (p, new_snapshot)
      else v_perms.perm_map x
    )
  } in
  same_prefix_same_sum_until v_perms.perm_map v_perms'.perm_map v_perms.current_max;
  only_one_live_pid_with_full_permission' v_perms' pid;
  assert(forall (pid:live_pid' v_perms'). get_snapshot_from_pid' v_perms' pid == new_snapshot);
  v_perms'
