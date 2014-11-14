(*
   Copyright 2008-2014 Nikhil Swamy and Microsoft Research

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
module ST
open Prims.STATE

(* stateful primitives in F*, currently just simply typed; soon to be monadically typed *)

assume val alloc: 'a -> ref 'a
assume val read: r:ref 'a -> State 'a (fun 'p h -> forall x. x==SelHeap h r ==> 'p x h)
assume val write: r:ref 'a -> v:'a -> State unit (fun 'p h -> forall h1. h1==UpdHeap h r v ==> 'p () h1) 
