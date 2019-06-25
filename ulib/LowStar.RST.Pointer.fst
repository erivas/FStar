(*
   Copyright 2008-2019 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
module LowStar.RST.Pointer

open FStar.HyperStack.ST
module A = LowStar.Array
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module Seq = FStar.Seq
module P = LowStar.Permissions

open LowStar.Resource
open LowStar.RST

open LowStar.BufferOps

(* View and resource for (heap-allocated, freeable) pointer resources *)

type vptr (a: Type) = {
  x: a;
  p: P.permission
}

abstract
let ptr_view (#a:Type) (ptr:A.array a) : view (vptr a) = 
  reveal_view ();
  let fp = Ghost.hide (A.loc_array ptr) in 
  let inv h = A.live h ptr /\ A.freeable ptr /\ A.vlength ptr = 1 in
  let sel h = {x = Seq.index (A.as_seq h ptr) 0; p = A.get_perm h ptr 0} in
  {
    fp = fp;
    inv = inv;
    sel = sel
  }

let ptr_resource (#a:Type) (ptr:A.array a) = 
  as_resource (ptr_view ptr)

let reveal_ptr ()
  : Lemma ((forall a (ptr:A.array a) .{:pattern as_loc (fp (ptr_resource ptr))} 
             as_loc (fp (ptr_resource ptr)) == A.loc_array ptr) /\
           (forall a (ptr:A.array a) h .{:pattern inv (ptr_resource ptr) h} 
             inv (ptr_resource ptr) h <==> A.live h ptr /\ A.freeable ptr /\ A.vlength ptr = 1) /\
           (forall a (ptr:A.array a) h .{:pattern sel (ptr_view ptr) h} 
             sel (ptr_view ptr) h == { x = Seq.index (A.as_seq h ptr) 0; p = A.get_perm h ptr 0})) = 
  ()

(* Reading and writing using a pointer resource *)

let ptr_read (#a:Type)
             (ptr:A.array a)
           : RST a (ptr_resource ptr)
                   (fun _ -> ptr_resource ptr)
                   (fun _ -> True)
                   (fun h0 x h1 -> 
                      (sel (ptr_view ptr) h0).x == x /\ 
                      sel (ptr_view ptr) h0 == sel (ptr_view ptr) h1) =
  A.index ptr 0ul

let ptr_write (#a:Type)
              (ptr:A.array a)
              (x:a)
            : RST unit (ptr_resource ptr)
                       (fun _ -> ptr_resource ptr)
                       (fun h -> P.allows_write (sel (ptr_view ptr) h).p)
                       (fun h0 _ h1 -> 
                          (sel (ptr_view ptr) h0).p == (sel (ptr_view ptr) h1).p /\
                          (sel (ptr_view ptr) h1).x == x) =
  reveal_rst_inv ();
  reveal_modifies ();
  A.upd ptr 0ul x


(* Unscoped allocation and deallocation of pointer resources *)

let ptr_alloc (#a:Type)
              (init:a)
            : RST (A.array a) (empty_resource)
                                (fun ptr -> ptr_resource ptr)
                                (fun _ -> True)
                                (fun _ ptr h1 -> 
                                   sel (ptr_view ptr) h1 == {x = init; p = FStar.Real.one}) =
  reveal_rst_inv ();
  reveal_modifies ();
  A.alloc init 1ul

let ptr_free (#a:Type)
             (ptr:A.array a)
           : RST unit (ptr_resource ptr)
                      (fun ptr -> empty_resource)
                      (fun h -> P.allows_write (sel (ptr_view ptr) h).p)
                      (fun _ ptr h1 -> True) =
  reveal_rst_inv ();
  reveal_modifies ();
  reveal_empty_resource ();
  A.free ptr

(* Scoped allocation of (heap-allocated, freeable) pointer resources *)

unfold
let with_new_ptr_pre (res:resource) =
  pre:r_pre res{forall h0 h1 . 
                  pre h0 /\ 
                  sel (view_of res) h0 == sel (view_of res) h1 
                  ==> 
                  pre h1}

unfold
let with_new_ptr_post (res0:resource) (a:Type) (res1:a -> resource) =
  post:r_post res0 a res1{forall h0 h1 x h2 h3 . 
                            sel (view_of res0) h0 == sel (view_of res0) h1 /\
                            post h1 x h2 /\
                            sel (view_of (res1 x)) h2 == sel (view_of (res1 x)) h3 
                            ==>
                            post h0 x h3}

let with_new_ptr (#res:resource)
                 (#a:Type)
                 (init:a)
                 (#b:Type)
                 (#pre:with_new_ptr_pre res)
                 (#post:with_new_ptr_post res b (fun _ -> res))
                 (f:(ptr:A.array a -> RST b (res <*> (ptr_resource ptr))
                                              (fun _ -> res <*> (ptr_resource ptr))
                                              (fun h -> pre h /\ sel (ptr_view ptr) h == {x = init; p = FStar.Real.one}) 
                                              (fun h0 x h1 -> post h0 x h1 /\ P.allows_write (sel (ptr_view ptr) h1).p))) 
               : RST b res (fun _ -> res) pre post = 
  reveal_star ();
  let ptr = 
    rst_frame 
      res 
      (fun ptr -> res <*> ptr_resource ptr)
      (fun _ -> ptr_alloc init) in
  let x = f ptr in 
  rst_frame
    (res <*> ptr_resource ptr)
    (fun _ -> res)
    (fun _ -> ptr_free ptr);
  x
