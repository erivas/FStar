module LowStar.Array

module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
open FStar.HyperStack.ST
module F = FStar.FunctionalExtensionality
module G = FStar.Ghost
module U32 = FStar.UInt32
module MG = FStar.ModifiesGen

open LowStar.Permissions

open FStar.Real

type value_with_perms (a: Type0) = vp : (a & Ghost.erased (perms_rec a)){
  let (v, p) = vp in
  forall (pid:live_pid (Ghost.reveal p)). get_snapshot_from_pid (Ghost.reveal p) pid == v
}

type with_perm (a: Type) = {
  wp_v: a;
  wp_perm: permission;
}

noeq type array (a:Type0) :Type0 =
  | Array:
    max_length:U32.t{U32.v max_length > 0} ->
    content:HST.reference (Seq.lseq (value_with_perms a) (U32.v max_length)) ->
    idx:U32.t ->
    length:U32.t{U32.v idx + U32.v length <= U32.v max_length /\ U32.v length > 0} ->
    pid:Ghost.erased perm_id ->
    array a

(*** Definitions of Ghost operations and predicates on arrays ***)

let length #a b = b.length

let as_seq #a h b =
  let s = HS.sel h b.content in
  Seq.init (vlength b) (fun x -> fst (Seq.index s (U32.v b.idx + x)))

let as_perm_seq (#a:Type) (h:HS.mem) (b: array a) : GTot (Seq.seq permission) =
  let s = HS.sel h b.content in
  Seq.init_ghost (vlength b) (fun x ->
    get_permission_from_pid (Ghost.reveal (snd (Seq.index s (U32.v b.idx + x)))) (Ghost.reveal b.pid)
  )

let live_cell (#a:Type) (h:HS.mem) (b:array a) (i:nat{i < vlength b}) : Type0 =
  get_perm #a h b i >. 0.0R /\ HS.contains h b.content

let as_perm_seq_pid (#a:Type) (h:HS.mem) (b: array a) (pid:perm_id) : GTot (Seq.seq permission) =
  let s = HS.sel h b.content in
  Seq.init_ghost (vlength b) (fun x ->
    get_permission_from_pid (Ghost.reveal (snd (Seq.index s (U32.v b.idx + x)))) pid
  )

let get_perm_pid (#a:Type) (h:HS.mem) (b:array a) (i:nat{i < vlength b}) (pid:perm_id) : GTot P.permission
  = Seq.index (as_perm_seq_pid h b pid) i

let cell_perm_pid (#a:Type) (h:HS.mem) (b:array a) (i:nat{i < vlength b}) (pid:perm_id) =
  Seq.index (as_perm_seq_pid #a h b pid) i

let live_cell_pid (#a:Type) (h:HS.mem) (b:array a) (i:nat{i < vlength b}) (pid:perm_id)
  : Type0 =
  cell_perm_pid #a h b i pid >. 0.0R /\ HS.contains h b.content

let live #a h b =
  HS.contains h b.content /\
  (forall (i:nat{i < vlength b}). live_cell h b i)

let sel (#a: Type0)  (h: HS.mem) (b: array a) (i:nat{i < vlength b}) : GTot (with_perm a) =
  let (_, perm_map) = Seq.index (HS.sel h b.content) (U32.v b.idx + i) in
  let perm = get_perm h b i in
  let snapshot = get h b i in
  { wp_v = snapshot; wp_perm = perm}

// Two arrays are mergeable (for permissions) if they correspond to the same subarray in the same array, and they have different pids
let mergeable #a b1 b2 =
  b1.max_length == b2.max_length /\
  b1.content == b2.content /\
  b1.idx == b2.idx /\
  b1.length == b2.length /\
  (Ghost.reveal b1.pid <> Ghost.reveal b2.pid)

let mergeable_same_length (#a:Type0) (b1 b2:array a) : Lemma
  (requires (mergeable b1 b2))
  (ensures (length b1 = length b2))
= ()

let mergeable_comm (#a: Type0) (b1 b2: array a): Lemma
  (requires (mergeable b1 b2))
  (ensures (mergeable b2 b1))
= ()

let frameOf (#a:Type0) (b:array a) : Tot HS.rid = HS.frameOf b.content
let as_addr (#a:Type0) (b:array a) : GTot nat = HS.as_addr b.content

let freeable #a b = b.idx = 0ul /\ b.max_length = b.length /\
  HS.is_mm b.content /\ HST.is_eternal_region (frameOf b)


(*** Sub-buffers *)


let gsub #a b i len =
    let b' = Array b.max_length b.content (U32.add b.idx i) len b.pid in
    let aux (h:HS.mem) : Lemma
      (as_seq h b' == Seq.slice (as_seq h b) (U32.v i) (U32.v i + U32.v len) /\
       as_perm_seq h b' == Seq.slice (as_perm_seq h b) (U32.v i) (U32.v i + U32.v len)) =
      let sb' = as_seq h b' in
      let sbslice =  Seq.slice (as_seq h b) (U32.v i) (U32.v i + U32.v len) in
      let sbp' =  as_perm_seq h b' in
      let sbpslice =  Seq.slice (as_perm_seq h b) (U32.v i) (U32.v i + U32.v len) in
      FStar.Seq.Base.lemma_eq_intro sb' sbslice;
      FStar.Seq.Base.lemma_eq_intro sbp' sbpslice
    in
    Classical.forall_intro aux;
    b'

let live_gsub #a h b i len =
  let b' = gsub b i len in
  let f1 (_ : squash (live h b))  : Lemma (live h b') =
    assert(forall (j:nat{j < vlength b'}). get_perm #a h b (U32.v i + j) >. 0.0R);
    assert(forall (j:nat{j < vlength b'}). get_perm #a h b' j >. 0.0R)
  in
  FStar.Classical.impl_intro f1

let len_gsub #a b i len' = ()

let frameOf_gsub #a b i len = ()

let as_addr_gsub #a b i len = ()

let gsub_inj #a b1 b2 i1 i2 len1 len2 = ()

let gsub_gsub #a b i1 len1 i2 len2 = ()

let gsub_zero_length #a b = ()

let msub #a b i len =
 Array b.max_length b.content (U32.add b.idx i) len b.pid

(*** Definitions of locations for arrays with permissions ***)

// We need to define the atomic locations cell per cell. We will then define loc_buffer as the union of aloc of cells
// The reason for this is that we want to prove that the loc of the union of two buffers corresponds to the union of locs
// of the two smaller buffers.
noeq
type ucell_ : Type0 = {
  b_max: nat;
  b_index:nat;
  b_pid:perm_id;
}

val ucell (region:HS.rid) (addr:nat) : Tot Type0
let ucell region addr = ucell_

// let uarray_of_array (#a:Type0) (b:array a) : Tot (uarray (frameOf b) (as_addr b)) =
//   { b_max_length = U32.v b.max_length;
//     b_offset = U32.v b.idx;
//     b_length = U32.v b.length;
//     b_pid = b.pid }

let ucell_preserved (#r:HS.rid) (#a:nat) (b:ucell r a) (h0 h1:HS.mem) : GTot Type0 =
  forall (t:Type0) (b':array t).
    (let i = b.b_index - U32.v b'.idx in // This cell corresponds to index i in the buffer
      (frameOf b' == r /\ as_addr b' == a /\ b'.pid == (Ghost.hide b.b_pid) /\ U32.v b'.max_length == b.b_max /\
        b.b_index >= U32.v b'.idx /\ b.b_index < U32.v b'.idx + U32.v b'.length /\ // If this cell is part of the buffer
        live_cell h0 b' i ==>
          live_cell h1 b' i /\ // If this cell is preserved, then its liveness is preserved
          (sel h0 b' i == sel h1 b' i))) // And its contents (snapshot + permission) are the same

let prove_loc_preserved (#r: HS.rid) (#a: nat) (loc: ucell r a) (h0 h1: HS.mem)
  (lemma: (t: Type0 -> b': array t -> Lemma
    (requires (
      let i = loc.b_index - U32.v b'.idx in
      frameOf b' == r /\ as_addr b' == a /\
      Ghost.reveal b'.pid == loc.b_pid /\ U32.v b'.max_length == loc.b_max /\
      loc.b_index >= U32.v b'.idx /\ loc.b_index < U32.v b'.idx + U32.v b'.length /\
      live_cell h0 b' i))
    (ensures (
      let i = loc.b_index - U32.v b'.idx in
      live_cell h1 b' i /\
      sel h0 b' i  == sel h1 b' i
      ))
  )) : Lemma (ucell_preserved #r #a loc h0 h1)
  =
  let aux (t: Type0) (b':array t) : Lemma(
      let i = loc.b_index - U32.v b'.idx in
      frameOf b' == r /\ as_addr b' == a /\
      Ghost.reveal b'.pid == loc.b_pid /\ U32.v b'.max_length == loc.b_max /\
      loc.b_index >= U32.v b'.idx /\ loc.b_index < U32.v b'.idx + U32.v b'.length /\
      live_cell h0 b' i ==>
        live_cell h1 b' i /\
        sel h0 b' i  == sel h1 b' i)
  =
  let aux' (_ : squash (
      let i = loc.b_index - U32.v b'.idx in
      frameOf b' == r /\ as_addr b' == a /\
      Ghost.reveal b'.pid == loc.b_pid /\ U32.v b'.max_length == loc.b_max /\
      loc.b_index >= U32.v b'.idx /\ loc.b_index < U32.v b'.idx + U32.v b'.length /\
      live_cell h0 b' i)
    ) : Lemma (
      let i = loc.b_index - U32.v b'.idx in
      loc.b_index >= U32.v b'.idx /\ loc.b_index < U32.v b'.idx + U32.v b'.length /\
      live_cell h1 b' i /\
      sel h0 b' i  == sel h1 b' i
    )
    = lemma t b'
  in
    Classical.impl_intro aux'
  in
  Classical.forall_intro_2 aux


// Two cells are included if they are equal: Same pid and same index in the buffer
let ucell_includes (#r: HS.rid) (#a: nat) (c1 c2: ucell r a) : GTot Type0 =
  c1.b_pid == c2.b_pid /\
  c1.b_index == c2.b_index /\
  c1.b_max == c2.b_max


let ucell_disjoint (#r:HS.rid) (#a:nat) (c1 c2:ucell r a) : GTot Type0 =
  c1.b_max == c2.b_max /\
    (c1.b_index <> c2.b_index \/           // Either the cells are different (i.e. spatially disjoint)
    c1.b_pid <> c2.b_pid)                 // Or they don't have the same permission

let cls : MG.cls ucell = MG.Cls #ucell
  ucell_includes
  (fun #r #a x -> ())
  (fun #r #a x1 x2 x3 -> ())
  ucell_disjoint
  (fun #r #a x1 x2 -> ())
  (fun #r #a larger1 larger2 smaller1 smaller2 -> ())
  ucell_preserved
  (fun #r #a x h -> ())
  (fun #r #a x h1 h2 h3 -> ())
  (fun #r #a b h1 h2 f ->
    prove_loc_preserved #r #a b h1 h2 (fun t b' ->
      let ref_t = Seq.lseq (value_with_perms t) (U32.v b'.max_length) in
      f ref_t (Heap.trivial_preorder ref_t) b'.content
    )
  )

let loc = MG.loc cls

let loc_none = MG.loc_none #ucell #cls
let loc_union (l1 l2:loc) = MG.loc_union #ucell #cls l1 l2
let loc_disjoint (l1 l2:loc) = MG.loc_disjoint #ucell #cls l1 l2
let loc_includes (l1 l2:loc) = MG.loc_includes #ucell #cls l1 l2

let aloc_cell (#a:Type) (b:array a) (i:nat{i < vlength b}) : GTot (ucell (frameOf b) (as_addr b)) =
  let r = frameOf b in
  let a = as_addr b in
  {
    b_max = U32.v b.max_length;
    b_index = U32.v b.idx + i;       // The index of the cell is the index inside the bigger array
    b_pid = (Ghost.reveal b.pid);
  }

let loc_cell (#t:Type) (b:array t) (i:nat{i < vlength b}) : GTot loc =
  let r = frameOf b in
  let a = as_addr b in
  MG.loc_of_aloc #ucell #cls #r #a (aloc_cell #t b i)

// The location of an array is the recursive union of all of its cells
let rec compute_loc_array (#a:Type) (b:array a) (i:nat{i <= vlength b})
  : GTot loc
  (decreases (vlength b - i))
  = if i = vlength b then MG.loc_none
    else loc_cell b i `MG.loc_union #ucell #cls` compute_loc_array b (i+1)

let loc_array (#a:Type) (b:array a) : GTot loc =
  compute_loc_array b 0

// The location of a cell of the array is included in the global loc_array
let lemma_includes_loc_cell_loc_array (#a:Type) (b:array a) (i:nat{i < vlength b})
  : Lemma (loc_includes (loc_array b) (loc_cell b i))
  =
  let rec aux (j:nat{j <= i}) : Lemma
    (ensures loc_includes (compute_loc_array b j) (loc_cell b i))
    (decreases (i - j))
    =
    if j = i then begin
      MG.loc_includes_refl #ucell #cls (loc_cell b i);
      MG.loc_includes_union_l #ucell #cls (loc_cell b i) (compute_loc_array b (j+1)) (loc_cell b i)
    end else begin
      aux (j+1);
      MG.loc_includes_union_l #ucell #cls (loc_cell b j) (compute_loc_array b (j+1)) (loc_cell b i)
    end
  in aux 0

let lemma_disjoint_pid_disjoint_cells (#a:Type) (b1 b2:array a) (i1:nat{i1 < vlength b1}) (i2:nat{i2 < vlength b2}) : Lemma
  (requires Ghost.reveal b1.pid <> Ghost.reveal b2.pid /\ b1.max_length == b2.max_length)
  (ensures loc_disjoint (loc_cell b1 i1) (loc_cell b2 i2))
  =
  let r1 = frameOf b1 in
  let r2 = frameOf b2 in
  let a1 = as_addr b1 in
  let a2 = as_addr b2 in
  let aloc1 = {
    b_max = U32.v b1.max_length;
    b_index = U32.v b1.idx + i1;
    b_pid = (Ghost.reveal b1.pid)
  } in
  let aloc2 = {
    b_max = U32.v b2.max_length;
    b_index = U32.v b2.idx + i2;
    b_pid = (Ghost.reveal b2.pid)
  } in
  MG.loc_disjoint_aloc_intro #ucell #cls #r1 #a1 #r2 #a2 aloc1 aloc2

let rec lemma_disjoint_pid_disjoint_cell_array (#a:Type0) (b1 b2:array a) (i:nat{i < vlength b1}) (j:nat{j <= vlength b2}) : Lemma
  (requires Ghost.reveal b1.pid <> Ghost.reveal b2.pid /\ b1.max_length == b2.max_length)
  (ensures loc_disjoint (compute_loc_array b2 j) (loc_cell b1 i))
  (decreases (vlength b2 - j))
  = if j = vlength b2 then begin
       MG.loc_disjoint_none_r #ucell #cls (loc_cell b1 i);
       MG.loc_disjoint_sym (loc_cell b1 i) (compute_loc_array b2 j)
    end else begin
      lemma_disjoint_pid_disjoint_cell_array b1 b2 i (j+1);
      lemma_disjoint_pid_disjoint_cells b1 b2 i j;
      MG.loc_disjoint_sym (compute_loc_array b2 (j+1)) (loc_cell b1 i);
      MG.loc_disjoint_union_r #ucell #cls (loc_cell b1 i) (loc_cell b2 j) (compute_loc_array b2 (j+1));
      MG.loc_disjoint_sym (loc_cell b1 i) (compute_loc_array b2 j)
    end

let rec lemma_disjoint_pid_disjoint_compute_array (#a:Type) (b1 b2:array a) (i:nat{i <= vlength b1}) : Lemma
  (requires Ghost.reveal b1.pid <> Ghost.reveal b2.pid /\ b1.max_length == b2.max_length)
  (ensures loc_disjoint (loc_array b2)  (compute_loc_array b1 i) )
  (decreases (vlength b1 - i))
  = if i = vlength b1 then MG.loc_disjoint_none_r #ucell #cls (loc_array b2)
    else begin
      lemma_disjoint_pid_disjoint_cell_array b1 b2 i 0;
      lemma_disjoint_pid_disjoint_compute_array b1 b2 (i+1);
      MG.loc_disjoint_union_r #ucell #cls (loc_array b2) (loc_cell b1 i) (compute_loc_array b1 (i+1))
    end

let lemma_disjoint_pid_disjoint_arrays (#a:Type0) (b1 b2:array a) : Lemma
  (requires Ghost.reveal b1.pid <> Ghost.reveal b2.pid /\ b1.max_length == b2.max_length)
  (ensures loc_disjoint (loc_array b1) (loc_array b2))
  = lemma_disjoint_pid_disjoint_compute_array b1 b2 0;
    MG.loc_disjoint_sym (loc_array b2) (loc_array b1)

let loc_addresses = MG.loc_addresses #ucell #cls
let loc_regions = MG.loc_regions #ucell #cls

let loc_not_unused_in = MG.loc_not_unused_in _

let loc_unused_in = MG.loc_unused_in _

let modifies (s:loc) (h0 h1:HS.mem) : GTot Type0 = MG.modifies s h0 h1

let lemma_disjoint_loc_from_array_disjoint_from_cells (#t: Type) (b: array t) (p: loc)
  : Lemma (requires (loc_disjoint (loc_array b) p))
    (ensures (forall(i:nat{i < vlength b}). loc_disjoint (loc_cell b i) p))
  =
  let aux (i:nat{i < vlength b}) : Lemma (loc_disjoint (loc_cell b i) p) =
    lemma_includes_loc_cell_loc_array b i;
    MG.loc_includes_refl p;
    MG.loc_disjoint_includes
      (loc_array b) p
      (loc_cell b i) p
  in
  Classical.forall_intro aux

let modifies_array_elim #t b p h h' =
  lemma_disjoint_loc_from_array_disjoint_from_cells #t b p;
  assert(forall(i:nat{i < vlength b}). loc_disjoint (loc_cell b i) p);
  let aux (i:nat{i < vlength b}) : Lemma (ensures (ucell_preserved #(frameOf b) #(as_addr b) (aloc_cell b i) h h')) =
    MG.modifies_aloc_elim #ucell #cls #(frameOf b) #(as_addr b)
      (aloc_cell b i) p h h'
  in
  Classical.forall_intro aux;
  assert(forall(i:nat{i < vlength b}). ucell_preserved #(frameOf b) #(as_addr b) (aloc_cell b i) h h');
  assert(forall(i:nat{i < vlength b}). sel h b i == sel h' b i);
  assert(forall(i:nat{i < vlength b}). (sel h b i).wp_v == Seq.index (as_seq h b) i /\ (sel h' b i).wp_v == Seq.index (as_seq h' b) i);
  assert(forall(i:nat{i < vlength b}).
    (sel h b i).wp_perm == Seq.index (as_perm_seq h b) i /\
    (sel h' b i).wp_perm == Seq.index (as_perm_seq h' b) i
  );
  Seq.lemma_eq_intro (as_seq h b) (as_seq h' b);
  Seq.lemma_eq_intro (as_perm_seq h b) (as_perm_seq h' b);
  assert(as_seq h b  == as_seq h' b);
  assert(as_perm_seq h b  == as_perm_seq h' b);
  assert((forall (i:nat{i < vlength b}). live_cell h' b i /\ HS.contains h' b.content));
  assert(HS.contains h' b.content)

let loc_union_idem s = MG.loc_union_idem s
let loc_union_comm s1 s2 = MG.loc_union_comm s1 s2
let loc_union_assoc = MG.loc_union_assoc #ucell #cls

let loc_union_idem_1 s1 s2 = MG.loc_union_assoc s1 s1 s2; loc_union_idem s1
let loc_union_idem_2 s1 s2 = MG.loc_union_assoc s1 s2 s2

let loc_union_loc_none_l s = MG.loc_union_loc_none_l s
let loc_union_loc_none_r s = MG.loc_union_loc_none_r s
let loc_includes_refl s = MG.loc_includes_refl s
let loc_includes_trans_backwards s1 s2 s3 = MG.loc_includes_trans s1 s2 s3
let loc_includes_union_l s1 s2 s = MG.loc_includes_union_l s1 s2 s

let loc_includes_union_r s s1 s2 =
  Classical.move_requires (MG.loc_includes_union_r s s1) s2;
  Classical.move_requires (MG.loc_includes_union_l s1 s2) s1;
  Classical.move_requires (MG.loc_includes_union_l s1 s2) s2;
  Classical.move_requires (MG.loc_includes_trans s (loc_union s1 s2)) s1;
  Classical.move_requires (MG.loc_includes_trans s (loc_union s1 s2)) s2;
  MG.loc_includes_refl s1;
  MG.loc_includes_refl s2

let loc_includes_none s = MG.loc_includes_none s

let loc_includes_region_addresses preserve_liveness1 preserve_liveness2 s r a =
  MG.loc_includes_region_addresses #_ #cls preserve_liveness1 preserve_liveness2 s r a

let loc_includes_region_addresses' preserve_liveness r a = ()
let loc_includes_region_region preserve_liveness1 preserve_liveness2 s1 s2 =
  MG.loc_includes_region_region #_ #cls preserve_liveness1 preserve_liveness2 s1 s2
let loc_includes_region_region' preserve_liveness s = ()

let loc_includes_adresses_loc_cell (#a: Type) (b: array a) (preserve_liveness: bool) (i:nat{i < vlength b})
  : Lemma (
    loc_includes (loc_addresses preserve_liveness (frameOf b) (Set.singleton (as_addr b)))
      (loc_cell b i)
  )
= MG.loc_includes_addresses_aloc #ucell #cls preserve_liveness (frameOf b) (Set.singleton (as_addr b))
    #(as_addr b) (aloc_cell b i)

let rec loc_includes_adresses_loc_array_rec (#a: Type) (b: array a) (preserve_liveness: bool) (i:nat{i <= vlength b})
  : Lemma (requires True) (ensures (
    loc_includes (loc_addresses preserve_liveness (frameOf b) (Set.singleton (as_addr b)))
      (compute_loc_array b i)
   )) (decreases (vlength b - i))
= if i = vlength b then
    MG.loc_includes_none (loc_addresses preserve_liveness (frameOf b) (Set.singleton (as_addr b)))
  else begin
  loc_includes_adresses_loc_cell b preserve_liveness i;
  loc_includes_adresses_loc_array_rec b preserve_liveness (i+1);
  assert(loc_includes (loc_addresses preserve_liveness (frameOf b) (Set.singleton (as_addr b)))
    ((loc_cell b i) `loc_union` (compute_loc_array b (i + 1)))
  )
  end

let loc_includes_adresses_loc_array #a b preserve_liveness =
  loc_includes_adresses_loc_array_rec b preserve_liveness 0

let loc_includes_region_union_l preserve_liveness l s1 s2 =
  MG.loc_includes_region_union_l preserve_liveness l s1 s2

let loc_includes_addresses_addresses_1 preserve_liveness1 preserve_liveness2 r1 r2 s1 s2 =
  MG.loc_includes_addresses_addresses cls preserve_liveness1 preserve_liveness2 r1 s1 s2

let loc_includes_addresses_addresses_2 preserve_liveness r s = ()

let loc_disjoint_sym' s1 s2 =
  Classical.move_requires (MG.loc_disjoint_sym s1) s2;
  Classical.move_requires (MG.loc_disjoint_sym s2) s1

let loc_disjoint_none_r s = MG.loc_disjoint_none_r s

let loc_disjoint_union_r' s s1 s2 =
  Classical.move_requires (MG.loc_disjoint_union_r s s1) s2;
  loc_includes_union_l s1 s2 s1;
  loc_includes_union_l s1 s2 s2;
  Classical.move_requires (MG.loc_disjoint_includes s (loc_union s1 s2) s) s1;
  Classical.move_requires (MG.loc_disjoint_includes s (loc_union s1 s2) s) s2;
  MG.loc_includes_refl s

let loc_disjoint_includes p1 p2 p1' p2' = MG.loc_disjoint_includes p1 p2 p1' p2'

let loc_disjoint_includes_r b1 b2 b2' = loc_disjoint_includes b1 b2 b1 b2'

let loc_disjoint_addresses preserve_liveness1 preserve_liveness2 r1 r2 n1 n2 =
  MG.loc_disjoint_addresses #_ #cls preserve_liveness1 preserve_liveness2 r1 r2 n1 n2

let loc_disjoint_regions preserve_liveness1 preserve_liveness2 rs1 rs2 =
  MG.loc_disjoint_regions #_ #cls preserve_liveness1 preserve_liveness2 rs1 rs2

let modifies_live_region s h1 h2 r = MG.modifies_live_region s h1 h2 r

let modifies_mreference_elim #t #pre b p h h' = MG.modifies_mreference_elim b p h h'
let modifies_refl s h = MG.modifies_refl s h
let modifies_loc_includes s1 h h' s2 = MG.modifies_loc_includes s1 h h' s2

let address_liveness_insensitive_locs = MG.address_liveness_insensitive_locs _
let region_liveness_insensitive_locs = MG.region_liveness_insensitive_locs _

let address_liveness_insensitive_addresses r a = MG.loc_includes_address_liveness_insensitive_locs_addresses cls r a
let region_liveness_insensitive_addresses preserve_liveness r a =
  MG.loc_includes_region_liveness_insensitive_locs_loc_addresses cls preserve_liveness r a
let region_liveness_insensitive_regions rs = MG.loc_includes_region_liveness_insensitive_locs_loc_regions cls rs
let region_liveness_insensitive_address_liveness_insensitive =
  MG.loc_includes_region_liveness_insensitive_locs_address_liveness_insensitive_locs cls

let modifies_liveness_insensitive_mreference l1 l2 h h' #t #pre x = MG.modifies_preserves_liveness l1 l2 h h' x
let modifies_liveness_insensitive_mreference_weak l h h' #t #pre x = modifies_liveness_insensitive_mreference loc_none l h h' x
let modifies_liveness_insensitive_region l1 l2 h h' x = MG.modifies_preserves_region_liveness l1 l2 h h' x
let modifies_liveness_insensitive_region_mreference l1 l2 h h' #t #pre x = MG.modifies_preserves_region_liveness_reference l1 l2 h h' x
let modifies_liveness_insensitive_region_weak l2 h h' x = modifies_liveness_insensitive_region loc_none l2 h h' x
let modifies_liveness_insensitive_region_mreference_weak l2 h h' #t #pre x = modifies_liveness_insensitive_region_mreference loc_none l2 h h' x

let modifies_trans = MG.modifies_trans

let modifies_trans_linear l l_goal h1 h2 h3 = modifies_trans l h1 h2 l_goal h3

let no_upd_fresh_region r l h0 h1 = MG.no_upd_fresh_region r l h0 h1
let new_region_modifies m0 r0 col = MG.new_region_modifies cls m0 r0 col

let modifies_ralloc_post #a #rel i init h x h' = MG.modifies_ralloc_post #_ #cls i init h x h'
let modifies_free #a #rel r m = MG.modifies_free #_ #cls r m

let modifies_upd #t #pre r v h = MG.modifies_upd #_ #cls r v h

let fresh_frame_loc_not_unused_in_disjoint h0 h1 = MG.not_live_region_loc_not_unused_in_disjoint cls h0 (HS.get_tip h1)

let mreference_live_loc_not_unused_in #t #pre h r = MG.mreference_live_loc_not_unused_in cls h r
let mreference_unused_in_loc_unused_in #t #pre h r = MG.mreference_unused_in_loc_unused_in cls h r

let unused_in_not_unused_in_disjoint_2 l1 l2 l1' l2' h =
  MG.loc_includes_trans (loc_unused_in h) l1 l1' ;
  MG.loc_includes_trans (loc_not_unused_in h) l2 l2'  ;
  MG.loc_unused_in_not_unused_in_disjoint cls h ;
  MG.loc_disjoint_includes (loc_unused_in h) (loc_not_unused_in h) l1' l2'

let modifies_loc_unused_in l h1 h2 l' =
  modifies_loc_includes (address_liveness_insensitive_locs) h1 h2 l;
  MG.modifies_address_liveness_insensitive_unused_in cls h1 h2;
  MG.loc_includes_trans (loc_unused_in h1) (loc_unused_in h2) l'

let ralloc_post_fresh_loc #a #rel i init m0 x m1 = ()
let fresh_frame_modifies h0 h1 = MG.fresh_frame_modifies cls h0 h1
let popped_modifies h0 h1 = MG.popped_modifies cls h0 h1

let modifies_only_not_unused_in = MG.modifies_only_not_unused_in #ucell #cls
let modifies_remove_new_locs l_fresh l_aux l_goal h1 h2 h3 = modifies_only_not_unused_in l_goal h1 h3
let modifies_remove_fresh_frame h1 h2 h3 l =
   MG.loc_regions_unused_in cls h1 (HS.mod_set (Set.singleton (HS.get_tip h2)));
   modifies_only_not_unused_in l h1 h3

let live_same_arrays_equal_types
  (#a1: Type0)
  (#a2: Type0)
  (b1: array a1{U32.v b1.max_length > 0})
  (b2: array a2{U32.v b2.max_length > 0})
  (h: HS.mem)
  : Lemma (requires (
     frameOf b1 == frameOf b2 /\
     as_addr b1 == as_addr b2 /\
     HS.contains h b1.content /\
     HS.contains h b2.content))
   (ensures (a1 == a2 /\ HS.sel h b1.content == HS.sel h b2.content))
  =
  Heap.lemma_distinct_addrs_distinct_preorders ();
  Heap.lemma_distinct_addrs_distinct_mm ();
  let s1 = HS.sel h b1.content in
  let s2 = HS.sel h b2.content in
  let (_, vp1) = Seq.index s1 0 in
  let (_, vp2) = Seq.index s2 0 in
  Seq.lemma_equal_instances_implies_equal_types ()

let only_one_live_pid_with_full_permission_specific
  (#a: Type0)
  (#v: a)
  (v_perms: value_perms a v)
  (pid: perm_id)
  (pid':live_pid v_perms)
  : Lemma (requires (get_permission_from_pid v_perms pid == 1.0R))
    (ensures pid == pid')
  = only_one_live_pid_with_full_permission v_perms pid

(*** Stateful operations implementing the ghost specifications ***)


let index #a b i =
  (**) let open HST in
  (**) let h0 = get() in
  (**) assert (live_cell h0 b (U32.v i));
  let s = ! b.content in
  let ( v, _ ) = Seq.index s (U32.v b.idx + U32.v i) in
  v

#push-options "--z3rlimit 10"

let upd #a b i v =
  (**) let open HST in
  (**) let h0 = get() in
  let s = ! b.content in
  let sb0 = Seq.slice s (U32.v b.idx) (U32.v b.idx + U32.v b.length) in
  let (v_init, perm_map) = Seq.index s (U32.v b.idx + U32.v i) in
  (**) assert (writeable_cell h0 b (U32.v i));
  let sb1 = Seq.upd sb0 (U32.v i) (v, Ghost.hide (change_snapshot #a #v_init (Ghost.reveal perm_map) (Ghost.reveal b.pid) v)) in
  let s1 = Seq.replace_subseq s (U32.v b.idx) (U32.v b.idx + U32.v b.length) sb1 in
  b.content := s1;
  (**) let h1 = get() in
  (**) assert (as_seq h1 b `Seq.equal` Seq.upd (as_seq h0 b) (U32.v i) v);
  (**) let r = frameOf b in
  (**) let n = as_addr b in
  (**) MG.modifies_aloc_intro
  (**)   #ucell #cls
  (**)   #r #n
  (**)   ({b_max = U32.v b.max_length; b_index = U32.v b.idx + U32.v i; b_pid = (Ghost.reveal b.pid)})
  (**)   h0 h1
  (**)   (fun r -> ())
  (**)   (fun t pre b -> ())
  (**)   (fun t pre b -> ())
  (**)   (fun r n -> ())
  (**)   (fun aloc' ->
  (**)     let aloc = ({b_max = U32.v b.max_length; b_index = U32.v b.idx + U32.v i; b_pid = (Ghost.reveal b.pid)}) in
  (**)     let aux (t:Type0) (b':array t) : Lemma
  (**)       (requires (
  (**)         let i = aloc'.b_index - U32.v b'.idx in
  (**)         frameOf b' == r /\ as_addr b' == n /\ Ghost.reveal b'.pid == aloc'.b_pid /\ U32.v b'.max_length == aloc'.b_max /\
  (**)         aloc'.b_index >= U32.v b'.idx /\ aloc'.b_index < U32.v b'.idx + U32.v b'.length /\
  (**)         live_cell h0 b' i))
  (**)       (ensures (let i = aloc'.b_index - U32.v b'.idx in
  (**)        live_cell h1 b' i /\
  (**)        (sel h0 b' i == sel h1 b' i))) =
  (**)        live_same_arrays_equal_types b b' h0;
  (**)        if aloc.b_index = aloc'.b_index then begin
  (**)          let s0 = HS.sel h0 b.content in
  (**)          let (v0, vp0) = Seq.index s0 aloc.b_index in
  (**)          only_one_live_pid_with_full_permission_specific #a #v0 (Ghost.reveal vp0) aloc.b_pid aloc'.b_pid
  (**)        end
  (**)        else begin
  (**)          live_same_arrays_equal_types b b' h1
  (**)        end
  (**)     in
  (**)     prove_loc_preserved #r #n aloc' h0 h1 aux
  (**)   );
  (**) assert (modifies (loc_cell b (U32.v i)) h0 h1);
  (**) lemma_includes_loc_cell_loc_array b (U32.v i);
  (**) MG.modifies_loc_includes (loc_array b) h0 h1 (loc_cell b (U32.v i))

#pop-options

let alloc #a init len =
  let perm_map_pid = (
    let (vp, pid) = new_value_perms init true in
    ((vp <: perms_rec a), Ghost.hide pid)
  ) in
  let v = (init, Ghost.hide (fst perm_map_pid)) in
  let s = Seq.create (U32.v len) v in
  (**) let h0 = HST.get() in
  let content = HST.ralloc_mm HS.root s in
  (**) let h1 = HST.get() in
  (**) MG.modifies_ralloc_post #ucell #cls HS.root s h0 content h1;
  let b = Array len content 0ul len (snd perm_map_pid) in
  (**) assert (Seq.equal (as_seq h1 b) (Seq.create (U32.v len) init));
  b

let free #a b =
  (**) let h0 = HST.get () in
  HST.rfree b.content;
  (**) let h1 = HST.get () in
  (**) let r = frameOf b in
  (**) let n = as_addr b in
  (**) modifies_free #(Seq.lseq (value_with_perms a) (U32.v b.max_length))
  (**)   #(Heap.trivial_preorder (Seq.lseq (value_with_perms a) (U32.v b.max_length)))
  (**)   b.content h0
  (**) ;
  (**) assert(modifies (loc_freed_mreference b.content) h0 h1);
  (**) assume(modifies (loc_array b) h0 h1);
  ()

val share_cell
  (#a:Type0)
  (b:array a)
  (i:U32.t{U32.v i < vlength b})
  (pid:Ghost.erased perm_id)
  : Stack unit
  (requires (fun h0 ->
    live h0 b /\ (
      let (_, perm_map) = Seq.index (HS.sel h0 b.content) (U32.v b.idx + U32.v i) in
      Ghost.reveal pid > get_current_max (Ghost.reveal perm_map)
    )
  ))
  (ensures (fun h0 _ h1 ->
    modifies (loc_cell b (U32.v i)) h0 h1 /\
    live h1 b /\
    as_seq h0 b == as_seq h1 b /\ // The values of the initial array are not modified
    live_cell_pid h1 b (U32.v i) (Ghost.reveal pid) /\ // The cell is still live
    (forall (j:nat{j < vlength b}). // We only touch one cell
      j <> U32.v i ==> Seq.index (HS.sel h0 b.content) (U32.v b.idx + j) ==
        Seq.index (HS.sel h1 b.content) (U32.v b.idx + j)
    ) /\ // Permission is split into two
    get_perm h1 b (U32.v i) == P.half_permission (get_perm h0 b (U32.v i)) /\
    get_perm_pid h1 b (U32.v i) (Ghost.reveal pid) == P.half_permission (get_perm h0 b (U32.v i))
  ))

#push-options "--z3rlimit 10"

let share_cell #a b i pid =
  (**) let open HST in
  (**) let h0 = get() in
  let s = ! b.content in
  let sb0 = Seq.slice s (U32.v b.idx) (U32.v b.idx + U32.v b.length) in
  let (v_init, perm_map) = Seq.index s (U32.v b.idx + U32.v i) in
  (**) assert (live_cell h0 b (U32.v i));
  (**) lemma_live_pid_smaller_max (Ghost.reveal perm_map) (Ghost.reveal b.pid);
  let sb1 = Seq.upd sb0 (U32.v i)
    (v_init, Ghost.hide (share_perms_with_pid #a #v_init (Ghost.reveal perm_map) (Ghost.reveal b.pid) (Ghost.reveal pid)))
  in
  let s1 = Seq.replace_subseq s (U32.v b.idx) (U32.v b.idx + U32.v b.length) sb1 in
  b.content := s1;
  (**) let h1 = get() in
  (**) assert (as_seq h1 b `Seq.equal` as_seq h0 b);
  (**) let r = frameOf b in
  (**) let n = as_addr b in
  (**) MG.modifies_aloc_intro
  (**)   #ucell #cls
  (**)   #r #n
  (**)   ({b_max = U32.v b.max_length; b_index = U32.v b.idx + U32.v i; b_pid = Ghost.reveal b.pid})
  (**)   h0 h1
  (**)   (fun r -> ())
  (**)   (fun t pre b -> ())
  (**)   (fun t pre b -> ())
  (**)   (fun r n -> ())
  (**)   (fun aloc' ->
  (**)      prove_loc_preserved #r #n aloc' h0 h1 (fun t b'->
  (**)        live_same_arrays_equal_types b b' h0;
  (**)        live_same_arrays_equal_types b b' h1;
  (**)        if aloc'.b_index <> U32.v b.idx + U32.v i then ()
  (**)        else lemma_greater_max_not_live_pid (Ghost.reveal perm_map) (Ghost.reveal pid)
  (**)      )
  (**)     )

#pop-options

val share_cells
  (#a:Type0)
  (b:array a)
  (i:U32.t{U32.v i <= vlength b})
  (pid:Ghost.erased perm_id)
  : Stack unit
  (requires (fun h0 -> live h0 b /\
    (forall (j:nat{j < vlength b}). j >= U32.v i ==> (
      let (_, perm_map) = Seq.index (HS.sel h0 b.content) (U32.v b.idx + j) in
      Ghost.reveal pid > get_current_max (Ghost.reveal perm_map)
    ))
  ))
  (ensures (fun h0 b' h1 ->
    modifies (compute_loc_array b (U32.v i)) h0 h1 /\
    live h1 b /\
    as_seq h0 b == as_seq h1 b /\ // The values of the initial array are not modified
    (forall (j:nat{j < vlength b}). j < U32.v i ==> // We haven't modified the beginning
      Seq.index (HS.sel h0 b.content) (U32.v b.idx + j) == Seq.index (HS.sel h1 b.content) (U32.v b.idx + j)
    ) /\
    (forall (j:nat{j < vlength b}). j >= U32.v i ==> // Cells atr still live but permissiosn are halved
      live_cell_pid h1 b j (Ghost.reveal pid) /\
      get_perm h1 b j == P.half_permission (get_perm h0 b j) /\
      get_perm_pid h1 b j (Ghost.reveal pid) == P.half_permission (get_perm h0 b j)
    )
  ))

let rec share_cells #a b i pid =
  (**) let h0 = HST.get() in
  if U32.v i >= vlength b then
    (**) MG.modifies_none_intro #ucell #cls h0 h0
    (**)   (fun _ -> ())
    (**)   (fun _ _ _ -> ())
    (**)   (fun _ _ -> ())
  else begin
    share_cells b (U32.add i 1ul) pid;
    (**) let h1 = HST.get() in
    share_cell b i pid;
    (**) let h2 = HST.get () in
    (**) let s12 = compute_loc_array b (U32.v i + 1) in
    (**) let s23 = loc_cell b (U32.v i) in
    (**) MG.loc_union_comm #ucell #cls s12 s23;
    (**) MG.modifies_trans #ucell #cls s12 h0 h1 s23 h2
  end

val get_array_current_max (#a:Type0) (h:HS.mem) (b:array a) (i:U32.t{U32.v i <= vlength b}) : Pure (Ghost.erased perm_id)
  (requires True)
  (ensures fun pid -> forall (j:nat{j < vlength b}). j >= U32.v i ==>
    (let (_, perm_map) = Seq.index (HS.sel h b.content) (U32.v b.idx + j) in
      Ghost.reveal pid > get_current_max (Ghost.reveal perm_map)))
  (decreases (vlength b - U32.v i))

let rec get_array_current_max #a h b i =
  if U32.v i = vlength b then (Ghost.hide 1)
  else  begin
    let max_end = get_array_current_max h b (U32.add i 1ul) in
    let (v, perm_map) = Seq.index (HS.sel h b.content) (U32.v b.idx + U32.v i) in
    let current_max = Ghost.hide (get_current_max (Ghost.reveal perm_map) + 1) in
    Ghost.elift2 (fun (a b:perm_id) -> if a > b then a else b) max_end current_max
  end

val lemma_different_live_pid (#a:Type0) (h:HS.mem) (b:array a{vlength b > 0}) : Lemma
  (requires live h b)
  (ensures Ghost.reveal (get_array_current_max h b 0ul) <> Ghost.reveal b.pid)

let lemma_different_live_pid #a h b =
  let (_, perm_map) = Seq.index (HS.sel h b.content) (U32.v b.idx) in
  assert (live_cell h b 0);
  lemma_live_pid_smaller_max (Ghost.reveal perm_map) (Ghost.reveal b.pid)


let share #a b =
  (**) let open HST in
  (**) let h0 = get() in
  let new_pid = get_array_current_max h0 b 0ul in
  share_cells b 0ul new_pid;
  (**) let h1 = get() in
  let b' = Array b.max_length b.content b.idx b.length new_pid in
  (**) assert (as_seq h1 b' `Seq.equal` as_seq h0 b);
  (**) lemma_different_live_pid h0 b;
  (**) lemma_disjoint_pid_disjoint_arrays b b';
  b'

val merge_cell:
  #a: Type ->
  b: array a ->
  b1: array a ->
  i:U32.t{U32.v i < vlength b} ->
  Stack unit (requires (fun h0 ->
    mergeable b b1 /\
    live h0 b /\ live_cell h0 b1 (U32.v i) /\ HS.contains h0 b1.content /\
    P.summable_permissions (sel h0 b (U32.v i)).wp_perm (sel h0 b1 (U32.v i)).wp_perm
  ))
  (ensures (fun h0 _ h1 ->
    live h1 b /\ HS.contains h1 b1.content /\
    as_seq h0 b == as_seq h1 b /\
    (sel h1 b (U32.v i)).wp_perm = sum_permissions (sel h0 b (U32.v i)).wp_perm (sel h0 b1 (U32.v i)).wp_perm /\
    (sel h1 b (U32.v i)).wp_v == (sel h0 b (U32.v i)).wp_v /\
    (forall (j:nat{j <> U32.v i /\ j < vlength b}). sel h0 b j == sel h1 b j /\ sel h0 b1 j == sel h1 b1 j) /\
    modifies (loc_cell b (U32.v i) `loc_union` loc_cell b1 (U32.v i)) h0 h1
  ))

let merge_cell #a b b1 i =
 let open HST in
  (**) let h0 = HST.get () in
  let s0 = !b.content in
  let (v_init, perm_map) = Seq.index s0 (U32.v b.idx + U32.v i) in
  let s1 = Seq.upd s0 (U32.v b.idx + U32.v i) (v_init, Ghost.hide (
    merge_perms #a #v_init (Ghost.reveal perm_map) (Ghost.reveal b.pid) (Ghost.reveal b1.pid)
  )) in
  b.content := s1;
  (**) let h1 = HST.get () in
  (**) assert (as_seq h1 b `Seq.equal` as_seq h0 b);
  (**) let r = frameOf b in
  (**) let n = as_addr b in
  (**) let acell = aloc_cell b (U32.v i) in
  (**) let cell = loc_cell b (U32.v i) in
  (**) let acell1 = aloc_cell b1 (U32.v i) in
  (**) let cell1 = loc_cell b1 (U32.v i) in
  (**) let l = cell `loc_union` cell1 in
  (**) MG.modifies_intro #ucell #cls
  (**)   l
  (**)   h0 h1
  (**)   (fun r -> ())
  (**)   (fun t pre ref ->
  (**)     MG.loc_includes_refl cell;
  (**)     MG.loc_includes_union_l cell cell1 cell;
  (**)     MG.loc_includes_refl (MG.loc_mreference #ucell #cls #t #pre ref);
  (**)     MG.loc_disjoint_includes
  (**)       (MG.loc_mreference ref)
  (**)       l
  (**)       (MG.loc_mreference ref)
  (**)       cell;
  (**)     MG.loc_disjoint_sym  (MG.loc_mreference ref) cell;
  (**)     MG.loc_disjoint_aloc_addresses_elim #ucell #cls #r #n acell
  (**)       true
  (**)       (HS.frameOf ref)
  (**)       (Set.singleton (HS.as_addr ref))
  (**)   )
  (**)   (fun t pre b -> ())
  (**)   (fun r n -> ())
  (**)   (fun r' n' loc' ->
  (**)     prove_loc_preserved #r' #n' loc' h0 h1 (fun t' b' ->
  (**)       MG.loc_includes_refl cell;
  (**)       MG.loc_includes_union_l cell cell1 cell;
  (**)       MG.loc_includes_refl (MG.loc_of_aloc #ucell #cls #r' #n' loc');
  (**)       MG.loc_disjoint_includes
  (**)         (MG.loc_of_aloc loc')
  (**)         l
  (**)         (MG.loc_of_aloc loc')
  (**)         cell;
  (**)       MG.loc_disjoint_sym (MG.loc_of_aloc loc') cell;
  (**)       MG.loc_includes_refl cell1;
  (**)       MG.loc_includes_union_l cell cell1 cell1;
  (**)       MG.loc_disjoint_includes
  (**)         (MG.loc_of_aloc loc')
  (**)         l
  (**)         (MG.loc_of_aloc loc')
  (**)         cell1;
  (**)       MG.loc_disjoint_sym (MG.loc_of_aloc loc') cell1;
  (**)       MG.loc_disjoint_aloc_elim #ucell #cls #r' #n' #r #n loc' acell;
  (**)       MG.loc_disjoint_aloc_elim #ucell #cls #r' #n' #r #n loc' acell1;
  (**)       let i' = loc'.b_index - U32.v b'.idx in
  (**)       let (_, new_perm_map) = Seq.index (HS.sel h1 b'.content) (U32.v b'.idx + i') in
  (**)       if r' = r && n' = n then begin
  (**)         live_same_arrays_equal_types b b' h0;
  (**)         live_same_arrays_equal_types b b' h1
  (**)       end else ()
  (**)     )
  (**)  )

let rec double_array_union_intro (#a: Type) (buf buf1: array a) (i:nat{i < vlength buf}) : Lemma
  (requires (mergeable buf buf1))
  (ensures (
      let s02 = compute_loc_array buf i `MG.loc_union` compute_loc_array buf1 i in
      let s12 = compute_loc_array buf (i + 1) `MG.loc_union` (compute_loc_array buf1 (i + 1)) in
      let s01 = loc_cell buf i `MG.loc_union` loc_cell buf1 i in
      s02 == s01 `MG.loc_union` s12
  ))
  (decreases (vlength buf - i))
  =
  assert(mergeable buf buf1) ;
  let lbi = compute_loc_array buf i in
  let lb1i = compute_loc_array buf1 i in
  let b = compute_loc_array buf (i + 1) in
  let d = compute_loc_array buf1 (i + 1) in
  let a = loc_cell buf i in
  let c = loc_cell buf1 i in
  let s02 = (compute_loc_array buf i) `MG.loc_union` (compute_loc_array buf1 i) in
  let s12 = b `MG.loc_union` d in
  let s01 = a `MG.loc_union` c in
  assert(compute_loc_array buf i == a `MG.loc_union` b);
  assert(compute_loc_array buf1 i == c `MG.loc_union` d);
  assert(s02 == s01 `MG.loc_union` s12  <==>
    (a `MG.loc_union` b) `MG.loc_union` (c `MG.loc_union` d) ==
    (a `MG.loc_union` c) `MG.loc_union` (b `MG.loc_union` d)
  );
  calc (==) {
     (a `MG.loc_union` b) `MG.loc_union` (c `MG.loc_union` d);
     (==) { MG.loc_union_assoc (a `MG.loc_union` b) c d }
     ((a `MG.loc_union` b) `MG.loc_union` c) `MG.loc_union` d;
     (==) { MG.loc_union_comm a b }
     ((b `MG.loc_union` a) `MG.loc_union` c) `MG.loc_union` d;
     (==) { MG.loc_union_assoc b a c}
     (b `MG.loc_union` (a `MG.loc_union` c)) `MG.loc_union` d;
     (==) { MG.loc_union_comm (a `MG.loc_union` c) b }
     ((a `MG.loc_union` c) `MG.loc_union` b) `MG.loc_union` d;
     (==) { MG.loc_union_assoc (a `MG.loc_union` c) b d }
     (a `MG.loc_union` c) `MG.loc_union` (b `MG.loc_union` d);
  }

val merge_cells:
  #a: Type ->
  b: array a ->
  b1: array a ->
  i:U32.t{U32.v i <= vlength b} ->
  Stack unit (requires (fun h0 ->
    mergeable b b1 /\
    live h0 b /\  HS.contains h0 b1.content /\
    (forall (j:nat{j < vlength b /\ j >= U32.v i}). live_cell h0 b1 j /\ P.summable_permissions (sel h0 b j).wp_perm (sel h0 b1 j).wp_perm)
  ))
  (ensures (fun h0 _ h1 ->
    modifies (compute_loc_array b (U32.v i) `MG.loc_union` compute_loc_array b1 (U32.v i)) h0 h1 /\
    as_seq h0 b == as_seq h1 b /\
    live h1 b /\ (forall (j:nat{j >= U32.v i /\ j < vlength b}).
      (sel h1 b j).wp_perm = sum_permissions (sel h0 b j).wp_perm (sel h0 b1 j).wp_perm /\
      (sel h1 b j).wp_v == (sel h0 b j).wp_v
    ) /\ (forall (j:nat{j < U32.v i /\ j < vlength b}).
      sel h1 b j ==  sel h0 b j
    )
  ))

let rec merge_cells #a b b1 i =
  (**) let h0 = HST.get () in
  if U32.v i >= vlength b then begin
    (**) MG.modifies_none_intro #ucell #cls h0 h0
    (**)   (fun _ -> ())
    (**)   (fun _ _ _ -> ())
    (**)   (fun _ _ -> ());
    (**) MG.loc_union_loc_none_l #ucell #cls (MG.loc_none)
  end else begin
    merge_cell #a b b1 i;
    (**) let h1 = HST.get () in
    (**) assert(forall (j:nat{j >=  U32.v i + 1 /\ j < vlength b}).
    (**)   live_cell h0 b1 j /\ sel h0 b1 j == sel h1 b1 j /\ live_cell h1 b1 j /\
    (**)   P.summable_permissions (sel h0 b j).wp_perm (sel h0 b1 j).wp_perm
    (**) );
    merge_cells #a b b1 (U32.add i 1ul);
    (**) let h2 = HST.get () in
    (**) let s02 = compute_loc_array b (U32.v i) `MG.loc_union` compute_loc_array b1 (U32.v i) in
    (**) let s12 = compute_loc_array b (U32.v i + 1) `MG.loc_union` (compute_loc_array b1 (U32.v i + 1)) in
    (**) let s01 = loc_cell b (U32.v i) `MG.loc_union` loc_cell b1 (U32.v i) in
    (**) MG.loc_union_comm #ucell #cls s01 s12;
    (**) MG.modifies_trans #ucell #cls s01 h0 h1 s12 h2;
    (**) double_array_union_intro b b1 (U32.v i);
    (**) assert(MG.modifies s02 h0 h2)
    (**)
  end;
  (**) let h2 = HST.get () in
  assert(MG.modifies (compute_loc_array b (U32.v i) `MG.loc_union` compute_loc_array b1 (U32.v i)) h0 h2)

let merge #a b b1 =
  merge_cells #a b b1 0ul;
  (**) let h1 = HST.get () in
  (**) assert(forall (i:nat{i < vlength b}). (sel h1 b i).wp_perm = get_perm h1 b i)
