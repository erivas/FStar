module LowStar.Array

module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
open FStar.HyperStack.ST
module U32 = FStar.UInt32
module P = LowStar.Permissions

val array (a:Type0): Type0

(*** Definitions of Ghost operations and predicates on arrays ***)

val length (#a:Type) (b:array a) : l:U32.t{U32.v l > 0}
let vlength (#a:Type) (b:array a) : pos = U32.v (length b)

val as_seq (#a:Type) (h:HS.mem) (b:array a) : GTot (s:Seq.seq a{Seq.length s == vlength b})

val as_perm_seq (#a:Type) (h:HS.mem) (b:array a) : GTot (s:Seq.seq P.permission{Seq.length s == vlength b})

let get (#a:Type) (h:HS.mem) (b:array a) (i:nat{i < vlength b}) : GTot a
  = Seq.index (as_seq h b) i

let get_perm (#a:Type) (h:HS.mem) (b:array a) (i:nat{i < vlength b}) : GTot P.permission
  = Seq.index (as_perm_seq h b) i


val live (#a:Type) (h:HS.mem) (b:array a) : Type0

let writeable_cell (#a:Type) (h:HS.mem) (b:array a) (i:nat{i < vlength b}) : Type0 =
  get_perm #a h b i == 1.0R /\ live #a h b

let writeable #a h b =
  live #a h b /\
  (forall (i:nat{i < vlength #a b}). writeable_cell h b i)


val mergeable (#a:Type0) (b1 b2:array a) : Type0

val mergeable_same_length (#a:Type0) (b1 b2:array a) : Lemma
  (requires (mergeable b1 b2))
  (ensures (length b1 = length b2))
  [SMTPatOr [
    [SMTPat (mergeable b1 b2); SMTPat (length b1)];
    [SMTPat (mergeable b1 b2); SMTPat (length b2)]
  ]]

val mergeable_comm (#a: Type0) (b1 b2: array a): Lemma
  (requires (mergeable b1 b2))
  (ensures (mergeable b2 b1))
  [SMTPat (mergeable b1 b2)]

let summable_permissions (#a: Type0) (h: HS.mem) (b1 b2: array a) : Type0 =
  mergeable #a b1 b2 /\
  (forall (i:nat{i < vlength #a b1}). P.summable_permissions (get_perm h b1 i) (get_perm h b2 i))

val frameOf (#a:Type0) (b:array a) : Tot HS.rid
val as_addr (#a:Type0) (b:array a) : GTot nat

val freeable (#a: Type) (b: array a) : GTot Type0


(*** Sub-bufers *)

val gsub (#a:Type0) (b:array a) (i:U32.t) (len:U32.t{U32.v len > 0})
  :Ghost (array a)
         (requires (U32.v i + U32.v len <= vlength b))
	 (ensures (fun b' ->
	   forall(h: HS.mem). {:pattern [as_seq h b'; as_perm_seq h b']}
	   as_seq h b' == Seq.slice (as_seq h b) (U32.v i) (U32.v i + U32.v len) /\
	   as_perm_seq h b' == Seq.slice (as_perm_seq h b) (U32.v i) (U32.v i + U32.v len)
	 ))

val live_gsub (#a:Type0) (h:HS.mem) (b:array a) (i:U32.t) (len:U32.t{U32.v len > 0})
  :Lemma (requires (U32.v i + U32.v len <= vlength b))
         (ensures  (live h b ==> (live h (gsub  b i len))))
         [SMTPat (live h (gsub  b i len))]

val len_gsub (#a:Type0) (b:array a) (i:U32.t) (len':U32.t{U32.v len' > 0})
  :Lemma (requires (U32.v i + U32.v len' <= vlength b))
         (ensures (length (gsub b i len') == len'))
         [SMTPatOr [
             [SMTPat (length (gsub b i len'))];
             [SMTPat (length (gsub b i len'))];
         ]]

val frameOf_gsub (#a:Type0) (b:array a) (i:U32.t) (len:U32.t{U32.v len > 0})
  :Lemma (requires (U32.v i + U32.v len <= vlength b))
         (ensures (frameOf (gsub b i len) == frameOf b))
  [SMTPat (frameOf (gsub  b i len))]

val as_addr_gsub (#a:Type0) (b:array a) (i:U32.t) (len:U32.t{U32.v len > 0})
  :Lemma (requires (U32.v i + U32.v len <= vlength b))
         (ensures (as_addr (gsub b i len) == as_addr b))
         [SMTPat (as_addr (gsub b i len))]

val gsub_inj (#a:Type0) (b1 b2:array a) (i1 i2:U32.t) (len1:U32.t{U32.v len1 > 0}) (len2:U32.t{U32.v len2 > 0})
  :Lemma (requires (U32.v i1 + U32.v len1 <= vlength b1 /\
                    U32.v i2 + U32.v len2 <= vlength b2 /\
		    gsub b1 i1 len1 === gsub b2 i2 len2))
         (ensures (len1 == len2 /\ (b1 == b2 ==> i1 == i2) /\ ((i1 == i2 /\ length b1 == length b2) ==> b1 == b2)))

val gsub_gsub (#a:Type0)
  (b:array a)
  (i1:U32.t) (len1:U32.t{U32.v len1 > 0})
  (i2: U32.t)  (len2:U32.t{U32.v len2 > 0})
  :Lemma (requires (U32.v i1 + U32.v len1 <= vlength b /\
                    U32.v i2 + U32.v len2 <= U32.v len1))
         (ensures  (gsub (gsub b i1 len1) i2 len2 == gsub b (U32.add i1 i2) len2))
         [SMTPat (gsub (gsub b i1 len1) i2 len2)]

val gsub_zero_length (#a:Type0) (b:array a)
  :Lemma (b == gsub  b 0ul (length b))

val msub (#a:Type0) (b:array a) (i:U32.t) (len:U32.t{U32.v len > 0})
  : Stack (array a)
    (requires (fun h ->
      U32.v i + U32.v len <= vlength b /\ live h b
    ))
    (ensures (fun h y h' ->
      h == h' /\ y == gsub b i len
    ))

(*** Definitions of locations for arrays with permissions ***)

val loc:Type0

val loc_none: loc
val loc_union (s1 s2: loc) : GTot loc
val loc_disjoint (s1 s2: loc) : GTot Type0
val loc_includes (s1 s2: loc) : GTot Type0

val loc_array (#a:Type0) (b:array a) : GTot loc

val loc_addresses
  (preserve_liveness: bool)
  (r: HS.rid)
  (n: Set.set nat)
: GTot loc

val loc_regions
  (preserve_liveness: bool)
  (r: Set.set HS.rid)
: GTot loc

/// ``loc_mreference b`` is the set of memory locations associated to a
/// reference ``b``, which is actually the set of memory locations
/// associated to the address of ``b``.

unfold
let loc_mreference
  (#a: Type)
  (#p: Preorder.preorder a)
  (b: HS.mreference a p)
: GTot loc
= loc_addresses true (HS.frameOf b) (Set.singleton (HS.as_addr b))

unfold
let loc_freed_mreference
  (#a: Type)
  (#p: Preorder.preorder a)
  (b: HS.mreference a p)
: GTot loc
= loc_addresses false (HS.frameOf b) (Set.singleton (HS.as_addr b))


/// ``loc_region_only r`` is the set of memory locations associated to a
/// region ``r`` but not any region ``r'`` that extends ``r`` (in the sense
/// of ``FStar.HyperStack.extends``.)

unfold
let loc_region_only
  (preserve_liveness: bool)
  (r: HS.rid)
: GTot loc
= loc_regions preserve_liveness (Set.singleton r)

/// ``loc_all_regions_from r`` is the set of all memory locations
/// associated to a region ``r`` and any region ``r'`` that transitively
/// extends ``r`` (in the sense of ``FStar.HyperStack.extends``,
/// e.g. nested stack frames.)

unfold
let loc_all_regions_from
  (preserve_liveness: bool)
  (r: HS.rid)
: GTot loc
= loc_regions preserve_liveness (HS.mod_set (Set.singleton r))

val loc_not_unused_in (h: HS.mem) : GTot loc

val loc_unused_in (h: HS.mem) : GTot loc

val modifies (s: loc) (h1 h2: HS.mem) : GTot Type0

(*** Lemmas about locations and modifies clauses ***)
val modifies_array_elim
  (#t: Type)
  (b: array t)
  (p : loc)
  (h h': HS.mem)
: Lemma
  (requires (
    live h b /\
    loc_disjoint (loc_array b) p /\
    modifies p h h'
  ))
  (ensures (
    as_seq h b  == as_seq h' b /\
    as_perm_seq h b == as_perm_seq h' b /\
    live h' b
  ))
  [SMTPatOr [
    [ SMTPat (modifies p h h'); SMTPat (as_seq h b) ];
    [ SMTPat (modifies p h h'); SMTPat (as_perm_seq h b) ];
    [ SMTPat (modifies p h h'); SMTPat (live h b) ];
    [ SMTPat (modifies p h h'); SMTPat (as_seq h' b) ];
    [ SMTPat (modifies p h h'); SMTPat (as_perm_seq h' b) ];
    [ SMTPat (modifies p h h'); SMTPat (live h' b) ];
  ]]


val loc_union_idem (s: loc) : Lemma
  (loc_union s s == s)
  [SMTPat (loc_union s s)]

val loc_union_comm (s1 s2: loc) : Lemma
  (loc_union s1 s2 == loc_union s2 s1)
  [SMTPat (loc_union s1 s2)]

val loc_union_assoc
  (s1 s2 s3: loc)
: Lemma
  (loc_union s1 (loc_union s2 s3) == loc_union (loc_union s1 s2) s3)

val loc_union_idem_1 (s1 s2: loc) : Lemma
  (loc_union s1 (loc_union s1 s2) == loc_union s1 s2)
  [SMTPat (loc_union s1 (loc_union s1 s2))]

val loc_union_idem_2 (s1 s2: loc) : Lemma
  (loc_union (loc_union s1 s2) s2 == loc_union s1 s2)
  [SMTPat (loc_union (loc_union s1 s2) s2)]

val loc_union_loc_none_l (s: loc) : Lemma
  (loc_union loc_none s == s)
  [SMTPat (loc_union loc_none s)]

val loc_union_loc_none_r (s: loc) : Lemma
  (loc_union s loc_none == s)
  [SMTPat (loc_union s loc_none)]

val loc_includes_refl (s: loc) : Lemma
  (loc_includes s s)
  [SMTPat (loc_includes s s)]

val loc_includes_trans_backwards (s1 s2 s3: loc) : Lemma
  (requires (loc_includes s1 s2 /\ loc_includes s2 s3))
  (ensures (loc_includes s1 s3))
  [SMTPat (loc_includes s1 s3); SMTPat (loc_includes s2 s3)]

val loc_includes_union_l (s1 s2 s: loc) : Lemma
  (requires (loc_includes s1 s \/ loc_includes s2 s))
  (ensures (loc_includes (loc_union s1 s2) s))
  [SMTPat (loc_includes (loc_union s1 s2) s)]

val loc_includes_union_r (s s1 s2: loc) : Lemma
  (loc_includes s (loc_union s1 s2) <==> (loc_includes s s1 /\ loc_includes s s2))
  [SMTPat (loc_includes s (loc_union s1 s2))]

val loc_includes_none (s: loc) : Lemma
  (loc_includes s loc_none)
  [SMTPat (loc_includes s loc_none)]

val loc_includes_region_addresses
  (preserve_liveness1: bool)
  (preserve_liveness2: bool)
  (s: Set.set HS.rid)
  (r: HS.rid)
  (a: Set.set nat)
: Lemma
  (requires (Set.mem r s))
  (ensures (loc_includes (loc_regions preserve_liveness1 s) (loc_addresses preserve_liveness2 r a)))
  [SMTPat (loc_includes (loc_regions preserve_liveness1 s) (loc_addresses preserve_liveness2 r a))]

val loc_includes_region_addresses'
  (preserve_liveness: bool)
  (r: HS.rid)
  (a: Set.set nat)
: Lemma
  (loc_includes (loc_regions true (Set.singleton r)) (loc_addresses preserve_liveness r a))
  [SMTPat (loc_addresses preserve_liveness r a)]

val loc_includes_region_region
  (preserve_liveness1: bool)
  (preserve_liveness2: bool)
  (s1 s2: Set.set HS.rid)
: Lemma
  (requires ((preserve_liveness1 ==> preserve_liveness2) /\ Set.subset s2 s1))
  (ensures (loc_includes (loc_regions preserve_liveness1 s1) (loc_regions preserve_liveness2 s2)))
  [SMTPat (loc_includes (loc_regions preserve_liveness1 s1) (loc_regions preserve_liveness2 s2))]

val loc_includes_region_region'
  (preserve_liveness: bool)
  (s: Set.set HS.rid)
: Lemma
  (loc_includes (loc_regions false s) (loc_regions preserve_liveness s))
  [SMTPat (loc_regions preserve_liveness s)]

val loc_includes_adresses_loc_array (#a: Type) (b: array a) (preserve_liveness: bool)
: Lemma (
    loc_includes (loc_addresses preserve_liveness (frameOf b) (Set.singleton (as_addr b)))
      (loc_array b)
  )
  [SMTPat (loc_addresses preserve_liveness (frameOf b) (Set.singleton (as_addr b)));
   SMTPat (loc_array b)]

val loc_includes_region_union_l
  (preserve_liveness: bool)
  (l: loc)
  (s1 s2: Set.set HS.rid)
: Lemma
  (requires (loc_includes l (loc_regions preserve_liveness (Set.intersect s2 (Set.complement s1)))))
  (ensures (loc_includes (loc_union (loc_regions preserve_liveness s1) l) (loc_regions preserve_liveness s2)))
  [SMTPat (loc_includes (loc_union (loc_regions preserve_liveness s1) l) (loc_regions preserve_liveness s2))]

val loc_includes_addresses_addresses_1
  (preserve_liveness1 preserve_liveness2: bool)
  (r1 r2: HS.rid)
  (s1 s2: Set.set nat)
: Lemma
  (requires (r1 == r2 /\ (preserve_liveness1 ==> preserve_liveness2) /\ Set.subset s2 s1))
  (ensures (loc_includes (loc_addresses preserve_liveness1 r1 s1) (loc_addresses preserve_liveness2 r2 s2)))
  [SMTPat (loc_includes (loc_addresses preserve_liveness1 r1 s1) (loc_addresses preserve_liveness2 r2 s2))]

val loc_includes_addresses_addresses_2
  (preserve_liveness: bool)
  (r: HS.rid)
  (s: Set.set nat)
: Lemma
  (loc_includes (loc_addresses false r s) (loc_addresses preserve_liveness r s))
  [SMTPat (loc_addresses preserve_liveness r s)]

val loc_disjoint_sym'
  (s1 s2: loc)
: Lemma
  (loc_disjoint s1 s2 <==> loc_disjoint s2 s1)
  [SMTPat (loc_disjoint s1 s2)]

val loc_disjoint_none_r
  (s: loc)
: Lemma
  (ensures (loc_disjoint s loc_none))
  [SMTPat (loc_disjoint s loc_none)]

val loc_disjoint_union_r'
  (s s1 s2: loc)
: Lemma
  (ensures (loc_disjoint s (loc_union s1 s2) <==> (loc_disjoint s s1 /\ loc_disjoint s s2)))
  [SMTPat (loc_disjoint s (loc_union s1 s2))]

val loc_disjoint_includes
  (p1 p2 p1' p2' : loc)
: Lemma
  (requires (loc_includes p1 p1' /\ loc_includes p2 p2' /\ loc_disjoint p1 p2))
  (ensures (loc_disjoint p1' p2'))

val loc_disjoint_includes_r (b1 : loc) (b2 b2': loc) : Lemma
  (requires (loc_includes b2 b2' /\ loc_disjoint b1 b2))
  (ensures (loc_disjoint b1 b2'))
  [SMTPat (loc_disjoint b1 b2'); SMTPat (loc_includes b2 b2')]

val loc_disjoint_addresses
  (preserve_liveness1 preserve_liveness2: bool)
  (r1 r2: HS.rid)
  (n1 n2: Set.set nat)
: Lemma
  (requires (r1 <> r2 \/ Set.subset (Set.intersect n1 n2) Set.empty))
  (ensures (loc_disjoint (loc_addresses preserve_liveness1 r1 n1) (loc_addresses preserve_liveness2 r2 n2)))
  [SMTPat (loc_disjoint (loc_addresses preserve_liveness1 r1 n1) (loc_addresses preserve_liveness2 r2 n2))]

val loc_disjoint_regions
  (preserve_liveness1: bool)
  (preserve_liveness2: bool)
  (rs1 rs2: Set.set HS.rid)
: Lemma
  (requires (Set.subset (Set.intersect rs1 rs2) Set.empty))
  (ensures (loc_disjoint (loc_regions preserve_liveness1 rs1) (loc_regions preserve_liveness2 rs2)))
  [SMTPat (loc_disjoint (loc_regions preserve_liveness1 rs1) (loc_regions preserve_liveness2 rs2))]


val modifies_live_region
  (s: loc)
  (h1 h2: HS.mem)
  (r: HS.rid)
: Lemma
  (requires (modifies s h1 h2 /\ loc_disjoint s (loc_region_only false r) /\ HS.live_region h1 r))
  (ensures (HS.live_region h2 r))
  [SMTPatOr [
    [SMTPat (modifies s h1 h2); SMTPat (HS.live_region h1 r)];
    [SMTPat (modifies s h1 h2); SMTPat (HS.live_region h2 r)];
  ]]

val modifies_mreference_elim
  (#t: Type)
  (#pre: Preorder.preorder t)
  (b: HS.mreference t pre)
  (p: loc)
  (h h': HS.mem)
: Lemma
  (requires (
    loc_disjoint (loc_mreference b) p /\
    HS.contains h b /\
    modifies p h h'
  ))
  (ensures (
    HS.contains h' b /\
    HS.sel h b == HS.sel h' b
  ))
  [SMTPatOr [
    [ SMTPat (modifies p h h'); SMTPat (HS.sel h b) ] ;
    [ SMTPat (modifies p h h'); SMTPat (HS.contains h b) ];
    [ SMTPat (modifies p h h'); SMTPat (HS.sel h' b) ] ;
    [ SMTPat (modifies p h h'); SMTPat (HS.contains h' b) ]
  ] ]

val modifies_refl
  (s: loc)
  (h: HS.mem)
: Lemma
  (modifies s h h)
  [SMTPat (modifies s h h)]

val modifies_loc_includes
  (s1: loc)
  (h h': HS.mem)
  (s2: loc)
: Lemma
  (requires (modifies s2 h h' /\ loc_includes s1 s2))
  (ensures (modifies s1 h h'))
  [SMTPat (modifies s1 h h'); SMTPat (modifies s2 h h')]

/// Some memory locations are tagged as liveness-insensitive: the
/// liveness preservation of a memory location only depends on its
/// disjointness from the liveness-sensitive memory locations of a
/// modifies clause.

val address_liveness_insensitive_locs: loc

val region_liveness_insensitive_locs: loc

val address_liveness_insensitive_addresses (r: HS.rid) (a: Set.set nat) : Lemma
  (address_liveness_insensitive_locs `loc_includes` (loc_addresses true r a))
  [SMTPat (address_liveness_insensitive_locs `loc_includes` (loc_addresses true r a))]

val region_liveness_insensitive_addresses (preserve_liveness: bool) (r: HS.rid) (a: Set.set nat) : Lemma
  (region_liveness_insensitive_locs `loc_includes` (loc_addresses preserve_liveness r a))
  [SMTPat (region_liveness_insensitive_locs `loc_includes` (loc_addresses preserve_liveness r a))]

val region_liveness_insensitive_regions (rs: Set.set HS.rid) : Lemma
  (region_liveness_insensitive_locs `loc_includes` (loc_regions true rs))
  [SMTPat (region_liveness_insensitive_locs `loc_includes` (loc_regions true rs))]

val region_liveness_insensitive_address_liveness_insensitive:
  squash (region_liveness_insensitive_locs `loc_includes` address_liveness_insensitive_locs)

val modifies_liveness_insensitive_mreference
  (l1 l2 : loc)
  (h h' : HS.mem)
  (#t: Type)
  (#pre: Preorder.preorder t)
  (x: HS.mreference t pre)
: Lemma
  (requires (modifies (loc_union l1 l2) h h' /\ loc_disjoint l1 (loc_mreference x) /\ address_liveness_insensitive_locs  `loc_includes` l2 /\ h `HS.contains` x))
  (ensures (h' `HS.contains` x))
  [SMTPatOr [
    [SMTPat (h `HS.contains` x); SMTPat (modifies (loc_union l1 l2) h h');];
    [SMTPat (h' `HS.contains` x); SMTPat (modifies (loc_union l1 l2) h h');];
  ]]

val modifies_liveness_insensitive_mreference_weak
  (l : loc)
  (h h' : HS.mem)
  (#t: Type)
  (#pre: Preorder.preorder t)
  (x: HS.mreference t pre)
 : Lemma (requires (modifies l h h' /\
                    address_liveness_insensitive_locs `loc_includes` l /\
		    h `HS.contains` x))
         (ensures  (h' `HS.contains` x))
         [SMTPatOr [
           [SMTPat (h `HS.contains` x); SMTPat (modifies l h h');];
           [SMTPat (h' `HS.contains` x); SMTPat (modifies l h h');];
         ]]

val modifies_liveness_insensitive_region
  (l1 l2 : loc)
  (h h' : HS.mem)
  (x: HS.rid)
: Lemma
  (requires (modifies (loc_union l1 l2) h h' /\ loc_disjoint l1 (loc_region_only false x) /\ region_liveness_insensitive_locs `loc_includes` l2 /\ HS.live_region h x))
  (ensures (HS.live_region h' x))
  [SMTPatOr [
    [SMTPat (modifies (loc_union l1 l2) h h'); SMTPat (HS.live_region h x)];
    [SMTPat (modifies (loc_union l1 l2) h h'); SMTPat (HS.live_region h' x)];
  ]]

val modifies_liveness_insensitive_region_mreference
  (l1 l2 : loc)
  (h h' : HS.mem)
  (#t: Type)
  (#pre: Preorder.preorder t)
  (x: HS.mreference t pre)
: Lemma
  (requires (modifies (loc_union l1 l2) h h' /\ loc_disjoint l1 (loc_mreference x) /\ region_liveness_insensitive_locs `loc_includes` l2 /\ HS.live_region h (HS.frameOf x)))
  (ensures (HS.live_region h' (HS.frameOf x)))
  [SMTPatOr [
    [SMTPat (modifies (loc_union l1 l2) h h'); SMTPat (HS.live_region h (HS.frameOf x))];
    [SMTPat (modifies (loc_union l1 l2) h h'); SMTPat (HS.live_region h' (HS.frameOf x))];
  ]]

val modifies_liveness_insensitive_region_weak
  (l2 : loc)
  (h h' : HS.mem)
  (x: HS.rid)
: Lemma
  (requires (modifies l2 h h' /\ region_liveness_insensitive_locs `loc_includes` l2 /\ HS.live_region h x))
  (ensures (HS.live_region h' x))
  [SMTPatOr [
    [SMTPat (modifies l2 h h'); SMTPat (HS.live_region h x)];
    [SMTPat (modifies l2 h h'); SMTPat (HS.live_region h' x)];
  ]]

val modifies_liveness_insensitive_region_mreference_weak
  (l2 : loc)
  (h h' : HS.mem)
  (#t: Type)
  (#pre: Preorder.preorder t)
  (x: HS.mreference t pre)
  : Lemma (requires (modifies l2 h h' /\
                     region_liveness_insensitive_locs `loc_includes` l2 /\
		     HS.live_region h (HS.frameOf x)))
          (ensures (HS.live_region h' (HS.frameOf x)))
          [SMTPatOr [
            [SMTPat (modifies l2 h h'); SMTPat (HS.live_region h (HS.frameOf x))];
            [SMTPat (modifies l2 h h'); SMTPat (HS.live_region h' (HS.frameOf x))];
          ]]

val modifies_address_liveness_insensitive_unused_in (h h' : HS.mem)
: Lemma
  (requires (modifies (address_liveness_insensitive_locs) h h'))
  (ensures (loc_not_unused_in h' `loc_includes` loc_not_unused_in h /\ loc_unused_in h `loc_includes` loc_unused_in h'))

val modifies_trans
  (s12: loc)
  (h1 h2: HS.mem)
  (s23: loc)
  (h3: HS.mem)
: Lemma
  (requires (modifies s12 h1 h2 /\ modifies s23 h2 h3))
  (ensures (modifies (loc_union s12 s23) h1 h3))

val modifies_trans_linear (l l_goal:loc) (h1 h2 h3:HS.mem)
  : Lemma (requires (modifies l h1 h2 /\ modifies l_goal h2 h3 /\ l_goal `loc_includes` l))
          (ensures  (modifies l_goal h1 h3))
	  [SMTPat (modifies l h1 h2); SMTPat (modifies l_goal h1 h3)]

val no_upd_fresh_region: r:HS.rid -> l:loc -> h0:HS.mem -> h1:HS.mem -> Lemma
  (requires (HS.fresh_region r h0 h1 /\ modifies (loc_union (loc_all_regions_from false r) l) h0 h1))
  (ensures  (modifies l h0 h1))
  [SMTPat (HS.fresh_region r h0 h1); SMTPat (modifies l h0 h1)]

val new_region_modifies (m0: HS.mem) (r0: HS.rid) (col: option int) : Lemma
  (requires (HST.is_eternal_region r0 /\ HS.live_region m0 r0 /\ (None? col \/ HS.is_eternal_color (Some?.v col))))
  (ensures (
    let (_, m1) = HS.new_eternal_region m0 r0 col in
    modifies loc_none m0 m1
  ))
  [SMTPat (HS.new_eternal_region m0 r0 col)]

val modifies_ralloc_post
  (#a: Type)
  (#rel: Preorder.preorder a)
  (i: HS.rid)
  (init: a)
  (h: HS.mem)
  (x: HST.mreference a rel { HST.is_eternal_region (HS.frameOf x) } )
  (h' : HS.mem)
: Lemma
  (requires (HST.ralloc_post i init h x h'))
  (ensures (modifies loc_none h h'))
  [SMTPat (HST.ralloc_post i init h x h')]

val modifies_free
  (#a: Type)
  (#rel: Preorder.preorder a)
  (r: HS.mreference a rel { HS.is_mm r } )
  (m: HS.mem { m `HS.contains` r } )
: Lemma
  (modifies (loc_freed_mreference r) m (HS.free r m))
  [SMTPat (HS.free r m)]

val modifies_upd
  (#t: Type) (#pre: Preorder.preorder t)
  (r: HS.mreference t pre)
  (v: t)
  (h: HS.mem)
: Lemma
  (requires (HS.contains h r))
  (ensures (modifies (loc_mreference r) h (HS.upd h r v)))
  [SMTPat (HS.upd h r v)]

val fresh_frame_loc_not_unused_in_disjoint
  (h0 h1: HS.mem)
: Lemma
  (requires (HS.fresh_frame h0 h1))
  (ensures (loc_disjoint (loc_region_only false (HS.get_tip h1)) (loc_not_unused_in h0)))
  [SMTPat (HS.fresh_frame h0 h1)]

val mreference_live_loc_not_unused_in
  (#t: Type)
  (#pre: Preorder.preorder t)
  (h: HS.mem)
  (r: HS.mreference t pre)
: Lemma
  (requires (h `HS.contains` r))
  (ensures (loc_not_unused_in h `loc_includes` loc_freed_mreference r /\ loc_not_unused_in h `loc_includes` loc_mreference r))
  [SMTPatOr [
    [SMTPat (HS.contains h r)];
    [SMTPat (loc_not_unused_in h `loc_includes` loc_mreference r)];
    [SMTPat (loc_not_unused_in h `loc_includes` loc_freed_mreference r)];
  ]]

val mreference_unused_in_loc_unused_in
  (#t: Type)
  (#pre: Preorder.preorder t)
  (h: HS.mem)
  (r: HS.mreference t pre)
: Lemma
  (requires (r `HS.unused_in` h))
  (ensures (loc_unused_in h `loc_includes` loc_freed_mreference r /\ loc_unused_in h `loc_includes` loc_mreference r))
  [SMTPatOr [
    [SMTPat (HS.unused_in r h)];
    [SMTPat (loc_unused_in h `loc_includes` loc_mreference r)];
    [SMTPat (loc_unused_in h `loc_includes` loc_freed_mreference r)];
  ]]

val unused_in_not_unused_in_disjoint_2
  (l1 l2 l1' l2': loc)
  (h: HS.mem)
: Lemma
  (requires (loc_unused_in h `loc_includes` l1 /\ loc_not_unused_in h `loc_includes` l2 /\ l1 `loc_includes` l1' /\ l2 `loc_includes` l2' ))
  (ensures (loc_disjoint l1'  l2' ))
  [SMTPat (loc_disjoint l1' l2'); SMTPat (loc_unused_in h `loc_includes` l1); SMTPat (loc_not_unused_in h `loc_includes` l2)]

val modifies_loc_unused_in
  (l: loc)
  (h1 h2: HS.mem)
  (l' : loc)
: Lemma
  (requires (
    modifies l h1 h2 /\
    address_liveness_insensitive_locs `loc_includes` l /\
    loc_unused_in h2 `loc_includes` l'
  ))
  (ensures (loc_unused_in h1 `loc_includes` l'))
  [SMTPatOr [
    [SMTPat (modifies l h1 h2); SMTPat (loc_unused_in h2 `loc_includes` l')];
    [SMTPat (modifies l h1 h2); SMTPat (loc_unused_in h1 `loc_includes` l')];
  ]]

let fresh_loc (l: loc) (h h' : HS.mem) : GTot Type0 =
  loc_unused_in h `loc_includes` l /\
  loc_not_unused_in h' `loc_includes` l

val ralloc_post_fresh_loc (#a:Type) (#rel:Preorder.preorder a) (i: HS.rid) (init:a) (m0: HS.mem)
                       (x: HST.mreference a rel{HS.is_eternal_region (HS.frameOf x)}) (m1: HS.mem) : Lemma
    (requires (HST.ralloc_post i init m0 x m1))
    (ensures (fresh_loc (loc_freed_mreference x) m0 m1))
    [SMTPat (HST.ralloc_post i init m0 x m1)]

//AR: this is needed for liveness across fresh_frame
val fresh_frame_modifies (h0 h1: HS.mem) : Lemma
  (requires (HS.fresh_frame h0 h1))
  (ensures  (modifies loc_none h0 h1))
  [SMTPat (HS.fresh_frame h0 h1)]

val popped_modifies (h0 h1: HS.mem) : Lemma
  (requires (HS.popped h0 h1))
  (ensures  (modifies (loc_region_only false (HS.get_tip h0)) h0 h1))
  [SMTPat (HS.popped h0 h1)]

val modifies_only_not_unused_in
  (l: loc)
  (h h' : HS.mem)
: Lemma
  (requires (modifies (loc_union (loc_unused_in h) l) h h'))
  (ensures (modifies l h h'))

val modifies_remove_new_locs (l_fresh l_aux l_goal:loc) (h1 h2 h3:HS.mem)
  : Lemma (requires (fresh_loc l_fresh h1 h2 /\
                     modifies l_aux h1 h2 /\
		     l_goal `loc_includes` l_aux /\
                     modifies (loc_union l_fresh l_goal) h2 h3))
          (ensures  (modifies l_goal h1 h3))
	  [SMTPat (fresh_loc l_fresh h1 h2);
	   SMTPat (modifies l_aux h1 h2);
	   SMTPat (modifies l_goal h1 h3)]

val modifies_remove_fresh_frame (h1 h2 h3:HS.mem) (l:loc)
  : Lemma (requires (HS.fresh_frame h1 h2 /\
                     modifies (loc_union (loc_all_regions_from false (HS.get_tip h2)) l) h2 h3))
          (ensures  (modifies l h1 h3))
	  [SMTPat (modifies l h1 h3); SMTPat (HS.fresh_frame h1 h2)]

(*** Stateful operations implementing the ghost specifications ***)


val index (#a:Type) (b:array a) (i:U32.t{U32.v i < vlength b})
  : Stack a (requires fun h -> live h b)
            (ensures fun h0 y h1 -> h0 == h1 /\ y == get h0 b (U32.v i))

val upd (#a:Type) (b:array a) (i:U32.t{U32.v i < vlength b}) (v:a) : Stack unit
  (requires fun h -> writeable_cell h b (U32.v i) /\ live h b)
  (ensures fun h0 _ h1 ->  writeable_cell h1 b (U32.v i) /\
    modifies (loc_array b) h0 h1 /\
    as_seq h1 b == Seq.upd (as_seq h0 b) (U32.v i) v /\
    as_perm_seq h1 b == as_perm_seq h0 b
  )

val alloc (#a:Type0) (init:a) (len:U32.t)
  : ST (array a)
       (requires fun _ -> U32.v len > 0)
       (ensures fun h0 b h1 ->
         modifies loc_none h0 h1 /\
         fresh_loc (loc_array b) h0 h1 /\
         writeable h1 b /\
         freeable b /\
         as_seq h1 b == Seq.create (U32.v len) init)

val free (#a: Type) (b: array a) : HST.ST unit
  (requires (fun h0 -> writeable h0 b /\ live  h0 b /\ freeable b))
  (ensures (fun h0 _ h1 ->
    Map.domain (HS.get_hmap h1) `Set.equal` Map.domain (HS.get_hmap h0) /\
    (HS.get_tip h1) == (HS.get_tip h0) /\
    modifies (loc_array b) h0 h1 /\
    HS.live_region h1 (frameOf b)
  ))

val share (#a:Type0) (b:array a) : Stack (array a)
  (requires fun h0 -> live h0 b /\ vlength b > 0)
  (ensures fun h0 b' h1 ->
    modifies (loc_array b) h0 h1 /\
    live h1 b /\ live h1 b' /\
    loc_disjoint (loc_array b) (loc_array b') /\
    as_seq h0 b == as_seq h1 b /\ // The values of the initial array are not modified
    as_seq h1 b' == as_seq h1 b /\ // The values of the new array are the same as the initial array
    mergeable b b' /\
    (forall (i:nat{i < vlength b}). {:pattern [get_perm h1 b' i; get_perm h1 b i] } // The permission gets split in two
      get_perm h1 b' i == P.half_permission (get_perm h0 b i) /\
      get_perm h1 b i == P.half_permission (get_perm h0 b i)
    ))

val merge:
  #a: Type ->
  b: array a ->
  b1: array a ->
  Stack unit (requires (fun h0 ->
    mergeable b b1 /\
    live h0 b /\ live h0 b1 /\
    (forall (i:nat{i < vlength b}). summable_permissions h0 b b1  )
  ))
  (ensures (fun h0 _ h1 ->
    live h1 b /\ (forall (i:nat{i < vlength b}). {:pattern (get_perm h1 b i)} // Permissions are summed into the first array
      get_perm h1 b i =  P.sum_permissions (get_perm h0 b i) (get_perm h0 b1 i)
    ) /\
    as_seq h1 b == as_seq h0 b /\ // The value of the array are not modifies
    modifies (loc_array b `loc_union` loc_array b1) h0 h1
  ))
