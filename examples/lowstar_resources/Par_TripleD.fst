module Par_TripleD

(*
  This module simplifies the Dijkstra Monads For All model in Par.fst.
  Instead of considering weakest preconditions, we here only consider
  Hoare triples.

    In short, we want parallel composition with the following (simplified) type

    val (<||>) (#a #b:Type)
               (#r0 #r1:resource)
               (#pre0:view r0 -> Type)
               (#pre1:view r1 -> Type)
               (#post0:a -> view r0 -> Type)
               (#post1:a -> view r1 -> Type)
               (c0:rst a r0 pre0 post0)
               (c1:rst b r1 pre1 post1)
             : RST (a & b) (r0 <*> r1) (pre0 /\ pre1) (post0 /\ post1)

*)

// The computational monad (free monad for the signature of { get , put , or }).
//
// This is a simple model of computation, supporting global state (2 locations
// storing natural numbers, locations modelled as booleans) and binary nondeterminism.
//
// Observe that parallel composition `||` is not part of the monad structure, because
// as is well known (cf the works of Plotkin et al), `||` is in fact a (binary) effect
// handler defined by recursion on the free monad structure (see below for details).
noeq
type m a =
  | Ret : a -> m a
  | Get : bool -> (nat -> m a) -> m a
  | Put : bool -> nat -> m a -> m a
  | MOr  : m a -> m a -> m a // MOr instead of Or to avoid name clashes with FStar.Reflection

// Functoriality of m
let rec map (#a:Type) (#b:Type) (f:a -> b) (c:m a) : Tot (m b) (decreases c) =
  match c with
  | Ret x -> Ret (f x)
  | Get b c -> Get b (fun n -> FStar.WellFounded.axiom1 c n; map f (c n))
  | Put b n c -> Put b n (map f c)
  | MOr c0 c1 -> MOr (map f c0) (map f c1)


// Below are two styles of defining the `||` operation. The first of these is more intuitive.

// Direct definition of parallel composition `||` as a combination of two mutually
// recursively defined left- and right-preferring parallel composition operators.
val l_par (#a:Type0) (#b:Type0) (c0:m a) (c1:m b) : Tot (m (a & b)) (decreases %[c0;c1])
val r_par (#a:Type0) (#b:Type0) (c0:m a) (c1:m b) : Tot (m (a & b)) (decreases %[c0;c1])

let pair_x (#a:Type) (x:a) = fun y -> (x, y)
let pair_y (#b:Type) (y:b) = fun x -> (x, y)

let rec l_get (#a:Type) (#b:Type) (c0':nat -> m a) (c1:m b) (n:nat) : Tot (m (a & b)) (decreases c0') =
  FStar.WellFounded.axiom1 c0' n;
  MOr (l_par (c0' n) c1) (r_par (c0' n) c1)

and l_par #a #b c0 c1 =
  match c0 with
  | Ret x -> map (pair_x x) c1
  | Get b c0' -> Get b (l_get c0' c1)
  | Put b n c0' -> Put b n (MOr (l_par c0' c1) (r_par c0' c1))
  | MOr c0' c0'' -> MOr (l_par c0' c1) (l_par c0'' c1)

and r_par #a #b c0 c1 =
  match c1 with
  | Ret y -> map (pair_y y) c0
  | Get b c1' -> Get b (fun n -> FStar.WellFounded.axiom1 c1' n; MOr (l_par c0 (c1' n)) (r_par c0 (c1' n)))
  | Put b n c1' -> Put b n (MOr (l_par c0 c1') (r_par c0 c1'))
  | MOr c1' c1'' -> MOr (r_par c0 c1') (r_par c0 c1'')

let m_par (#a #b:Type0) (c0:m a) (c1:m b) : m (a & b) =
  MOr (l_par c0 c1) (r_par c0 c1)

(*** Memory definitions ***)

/// For this example sketch, memory is simply a pair of booleans.
let mem = bool -> nat

let upd (b:bool) (n:nat) (h:mem) : mem =
  fun b' -> if b = b' then n else h b'

let loc = option bool

let modifies (fp:loc) (h0 h1:mem) =
  match fp with
  | None -> True
  | Some b -> h0 (not b) == h1 (not b)

/// Separating conjunction of two resources.
let xor a b = (a || b) && ((not a) || (not b))

/// In the current model, two locations are disjoint if they are not the whole memory (None) and if they are actually disjoint (xor of two resources)
let disjoint (l1 l2:loc) = Some? l1 /\ Some? l2 /\ xor (Some?.v l1) (Some?.v l2)

/// l2 is included in l1
let includes (l1 l2:loc) = 
  None? l1 \/ // l1 is the whole memory
  l1 == l2 // Or l1 is Some of something, and l2 needs to be the same

let loc_union (l1 l2:loc) : loc =
  match l1, l2 with
  | None, _ | _, None -> None
  | Some v1, Some v2 -> if v1 = v2 then Some v1 else None

/// We only consider predicates that are stable on the resource footprint: They depend only on the memory contents of the available resource
let is_stable_on (fp:loc) (pred:mem -> Type) =
  forall (h0 h1:mem) (l:loc). (pred h0 /\ modifies l h0 h1 /\ disjoint fp l) ==> pred h1

(*** Resource definitions ***)

/// Simple variant of our notion of resources.
let inv_reads_fp (fp:option bool) (inv:mem -> Type0) =
  forall h h' l. inv h /\ disjoint fp l /\ modifies l h h' ==> inv h'

noeq
type view_t a = {
  fp : option bool; (* none denotes owning both locations, TODO: account properly for owning neither location *)
  inv : mem -> Type0;
  sel : mem -> a
}

let view_t_refined a =
  view:view_t a{inv_reads_fp view.fp view.inv}

noeq
type resource = {
    t:Type0;
    view:view_t_refined t
  }

let (<*>) (r0 r1:resource) : resource =
  let t = r0.t & r1.t in
  let fp = None in
  let inv h = r0.view.inv h /\ r1.view.inv h /\
              Some? r0.view.fp /\ Some? r1.view.fp /\
              xor (Some?.v r0.view.fp) (Some?.v r1.view.fp)
  in
  let sel h = (r0.view.sel h,r1.view.sel h) in
  {
    t = t;
    view = {
      fp = fp;
      inv = inv;
      sel = sel
    }
  }

// Cannot leave this function unnamed inside chi definition to reason about it
let upd_pre (pre:mem -> Type) (b:bool) (n:nat) = fun h -> pre (upd b n h)
let upd_post (post:mem -> Type) (b:bool) (n:nat) = fun h -> post (upd b n h)

(*** Axiomatisation of the semantics, RST monad definition ***)

/// We assume here that the initial and final resources are the same
let rec chi #a (c:m a) (r:resource) (pre:mem -> Type) (post:mem -> Type) : Type =
  match c with
  | Ret x -> forall h. pre h ==> post h
  | Get b c ->
    includes r.view.fp (Some b) /\ // The accessed memory is inside the resource
    (forall h.
      (FStar.WellFounded.axiom1 c (h b);
      chi (c (h b)) r pre post))
  | Put b n c -> 
        includes r.view.fp (Some b) /\ // The updated memory is inside the resource
        // TODO: Equivalence is probably too strong. Should we rephrase chi to be {r.view.inv /\ pre}c{post /\ r.view.inv}
        // with resource invariants somehow outside of chi?
        (forall h. r.view.inv h <==> r.view.inv (upd b n h)) /\ // The resource invariant is preserved
        chi c r pre (upd_post post b n) // post
  | MOr c0 c1 -> chi c0 r pre post /\ chi c1 r pre post

let r_pred (pred:mem -> Type) (r:resource) = fun h -> pred h /\ r.view.inv h

/// The `is_stable_on predicate` is not yet provable in the current RST model:
/// pre/postconditions can currently refer to the whole memory, and not just the resource footprint
/// This will be resolved once selectors are implemented
let rst (a:Type) (r:resource) (pre post:mem -> Type) = c:m a{
  chi c r (r_pred pre r) (r_pred post r) /\
  is_stable_on r.view.fp pre /\ is_stable_on r.view.fp post}

/// Semantics of the monad
/// To resolve non-determinism for MOr, we use a stream of booleans to pick the left or right branch at each or instruction,
/// and a position number for knowing at which step of the stream we are
let rec run #a (c:m a) (h:mem) (pos:nat) (stream:nat -> bool) : a * mem =
  match c with
  | Ret x -> x, h
  | Get b c -> run (FStar.WellFounded.axiom1 c (h b); c (h b)) h pos stream
  | Put b n c -> run c (upd b n h) pos stream
  | MOr c0 c1 -> match stream pos with
                | false -> run c0 h (pos + 1) stream
                | true -> run c1 h (pos + 1) stream

/// The denotational semantics `run` and their axiomatisation `chi` should be coherent
/// More precisely, if we satisfy chi, then running the command `c` in a state satisfying the precondition
/// results in a state satisfying the postcondition, and only modifying the specified footprint
/// This would prove that Hoare triples accepted by chi always match the semantics
val lemma_chi_characterization (#a:Type) (c:m a) (r:resource) (pre:mem -> Type) (post:mem -> Type) (h0:mem) (pos:nat) (stream:nat -> bool) : Lemma
  (requires pre h0 /\ chi c r pre post)
  (ensures (
    let x, h1 = run c h0 pos stream in
    post h1 /\ modifies r.view.fp h0 h1)
  )
let rec lemma_chi_characterization #a c r pre post h0 pos stream =
  match c with
  | Ret x -> ()
  | Get b c -> lemma_chi_characterization (FStar.WellFounded.axiom1 c (h0 b); c (h0 b)) r pre post h0 pos stream
  | Put b n c -> admit ()
  | MOr c0 c1 -> lemma_chi_characterization c0 r pre post h0 (pos + 1) stream;
                lemma_chi_characterization c1 r pre post h0 (pos + 1) stream


// Resource for a single location (taken from Par.fst)
let loc_resource b =
  let fp = Some b in
  let inv h = True in
  let sel h = h b in
  {
    t = nat;
    view = {
      fp = fp;
      inv = inv;
      sel = sel
    }
  }

// Concrete case for lemma_chi_characterization
let c_pre : mem -> Type0 = fun h -> h false = 0
let c_post : mem -> Type0 = fun h -> h false = 1
let c_prog : m unit = Put false 1 (Put false 0 (Ret ()))
let c_res : resource = loc_resource false
let c_h0 : mem = fun b -> match b with
                       | false -> 0
                       | true -> 1
let c_pos : nat = 0
let c_stream : nat -> bool = fun n -> false
let c_h1 : mem = let x, h1 = run c_prog c_h0 c_pos c_stream in h1

let c_lemma_chi_pre (_ : unit) : Lemma (chi c_prog c_res c_pre c_post /\ c_pre c_h0) = ()
let c_lemma_chi_post (_ : unit) : Lemma ((c_post c_h1 /\ modifies c_res.view.fp c_h0 c_h1) ==> False) = ()
let absurd (_ : unit) : Lemma False =
  c_lemma_chi_pre ();
  c_lemma_chi_post ();
  lemma_chi_characterization c_prog c_res c_pre c_post c_h0 c_pos c_stream
