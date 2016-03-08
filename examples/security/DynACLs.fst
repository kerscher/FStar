module DynACLs
open Heap
open ST
(* type file = string *)

(* using dynamic ACLs in some database *)
type entry =
  | Readable of string
  | Writable of string
type db = list entry

let canWrite db file =
  is_Some (List.find (function Writable x -> x=file | _ -> false) db)

let canRead db file =
  is_Some (List.find (function Readable x | Writable x -> x=file) db)

assume val acls: ref db
logic type CanRead f h  = canRead  (Heap.sel h acls) f == true
logic type CanWrite f h = canWrite (Heap.sel h acls) f == true

let grant e =
  let a = ST.read acls in
  ST.write acls (e::a)

let revoke e =
  let a = ST.read acls in
  let db = List.filter (fun e' -> e<>e') a in
  ST.write acls db

(* two dangerous primitives *)
assume val read:   file:string -> ST string
                                     (requires (CanRead file))
                                     (ensures (fun h s h' -> h=h'))

assume val delete: file:string -> ST unit
                                     (requires (CanWrite file))
                                     (ensures (fun h s h' -> h=h'))

(* If you remove the name on this parameter, the verification of ACLs2.test fails, mysteriously *)
val safe_delete: file:string -> All unit
                (requires (fun h -> True))
                (ensures (fun h x h' -> h=h'))
let safe_delete file =
  if canWrite !acls file
  then delete file
  else failwith "unwritable"

val test_acls: file:string -> unit
let test_acls f =
  grant (Readable f);     (* ok *)
  let _ = read f in       (* ok --- it's in the acl *)
  (* delete f;               (\* not ok --- we're only allowed to read it *\) *)
  safe_delete f;          (* ok, but fails dynamically *)
  revoke (Readable f);
  (* let _ = read f in       (\* not ok any more *\) *)
  ()
