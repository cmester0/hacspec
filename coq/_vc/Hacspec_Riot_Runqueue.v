(** This file was automatically generated using Hacspec **)
Set Warnings "-notation-overridden,-ambiguous-paths".
Require Import Hacspec_Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
Require Import Hacspec_Lib.
Export Hacspec_Lib.

Definition uint32_bits_v : uint_size :=
  (usize 4) * (usize 8).

Definition n_queues_v : uint_size :=
  usize 20.

Definition n_threads_v : uint_size :=
  usize 30.

Definition sentinel_v : int8 :=
  @repr WORDSIZE8 255.

Inductive runqueue_id_t :=
| RunqueueId : int8 -> runqueue_id_t.

Inductive thread_id_t :=
| ThreadId : int8 -> thread_id_t.

Definition tail_t := nseq (int8) (n_queues_v).

Definition next_ids_t := nseq (int8) (n_threads_v).

Inductive clist_t :=
| Clist : (tail_t '× next_ids_t) -> clist_t.

Definition clist_new   : clist_t :=
  let tail_1197 : tail_t :=
    array_new_ (default : int8) (n_queues_v) in 
  let tail_1197 :=
    foldi (usize 0) (array_len (tail_1197)) (fun i_1198 tail_1197 =>
      let tail_1197 :=
        array_upd tail_1197 (i_1198) (sentinel_v) in 
      (tail_1197))
    tail_1197 in 
  let next_idxs_1199 : next_ids_t :=
    array_new_ (default : int8) (n_threads_v) in 
  let next_idxs_1199 :=
    foldi (usize 0) (array_len (next_idxs_1199)) (fun i_1200 next_idxs_1199 =>
      let next_idxs_1199 :=
        array_upd next_idxs_1199 (i_1200) (sentinel_v) in 
      (next_idxs_1199))
    next_idxs_1199 in 
  Clist ((tail_1197, next_idxs_1199)).


Definition clist_is_empty
  (x_1201 : clist_t)
  (rq_1202 : runqueue_id_t)
  
  : bool :=
  let 'RunqueueId (rq_1203) :=
    rq_1202 in 
  let 'Clist ((tail_1204, next_ids_1205)) :=
    x_1201 in 
  (array_index (tail_1204) (@cast _ uint32 _ (rq_1203))) =.? (sentinel_v).


Definition clist_push
  (x_1206 : clist_t)
  (n_1207 : thread_id_t)
  (rq_1208 : runqueue_id_t)
  
  : clist_t :=
  let 'RunqueueId (rq_1209) :=
    rq_1208 in 
  let 'ThreadId (n_1210) :=
    n_1207 in 
  let 'Clist ((tail_1211, next_idxs_1212)) :=
    x_1206 in 
  let '(tail_1211, next_idxs_1212) :=
    if (array_index (next_idxs_1212) (@cast _ uint32 _ (n_1210))) =.? (
      sentinel_v):bool then (let '(tail_1211, next_idxs_1212) :=
        if (array_index (tail_1211) (@cast _ uint32 _ (rq_1209))) =.? (
          sentinel_v):bool then (let tail_1211 :=
            array_upd tail_1211 (@cast _ uint32 _ (rq_1209)) (n_1210) in 
          let next_idxs_1212 :=
            array_upd next_idxs_1212 (@cast _ uint32 _ (n_1210)) (n_1210) in 
          (tail_1211, next_idxs_1212)) else (let next_idxs_1212 :=
            array_upd next_idxs_1212 (@cast _ uint32 _ (n_1210)) (array_index (
                next_idxs_1212) (@cast _ uint32 _ (array_index (tail_1211) (
                    @cast _ uint32 _ (rq_1209))))) in 
          let next_idxs_1212 :=
            array_upd next_idxs_1212 (@cast _ uint32 _ (array_index (
                  tail_1211) (@cast _ uint32 _ (rq_1209)))) (n_1210) in 
          let tail_1211 :=
            array_upd tail_1211 (@cast _ uint32 _ (rq_1209)) (n_1210) in 
          (tail_1211, next_idxs_1212)) in 
      (tail_1211, next_idxs_1212)) else ((tail_1211, next_idxs_1212)) in 
  Clist ((tail_1211, next_idxs_1212)).


Definition clist_pop_head
  (x_1213 : clist_t)
  (rq_1214 : runqueue_id_t)
  
  : (clist_t '× (option int8)) :=
  let 'RunqueueId (rq_1215) :=
    rq_1214 in 
  let 'Clist ((tail_1216, next_idxs_1217)) :=
    x_1213 in 
  let out_1218 : (option int8) :=
    @None int8 in 
  let '(tail_1216, next_idxs_1217, out_1218) :=
    if (array_index (tail_1216) (@cast _ uint32 _ (rq_1215))) =.? (
      sentinel_v):bool then ((tail_1216, next_idxs_1217, out_1218)) else (
      let head_1219 : int8 :=
        array_index (next_idxs_1217) (@cast _ uint32 _ (array_index (
              tail_1216) (@cast _ uint32 _ (rq_1215)))) in 
      let '(tail_1216, next_idxs_1217) :=
        if (head_1219) =.? (array_index (tail_1216) (@cast _ uint32 _ (
              rq_1215))):bool then (let tail_1216 :=
            array_upd tail_1216 (@cast _ uint32 _ (rq_1215)) (sentinel_v) in 
          (tail_1216, next_idxs_1217)) else (let next_idxs_1217 :=
            array_upd next_idxs_1217 (@cast _ uint32 _ (array_index (
                  tail_1216) (@cast _ uint32 _ (rq_1215)))) (array_index (
                next_idxs_1217) (@cast _ uint32 _ (head_1219))) in 
          (tail_1216, next_idxs_1217)) in 
      let next_idxs_1217 :=
        array_upd next_idxs_1217 (@cast _ uint32 _ (head_1219)) (sentinel_v) in 
      let out_1218 :=
        @Some int8 (head_1219) in 
      (tail_1216, next_idxs_1217, out_1218)) in 
  (Clist ((tail_1216, next_idxs_1217)), out_1218).


Definition clist_peek_head
  (x_1220 : clist_t)
  (rq_1221 : runqueue_id_t)
  
  : (option int8) :=
  let 'RunqueueId (rq_1222) :=
    rq_1221 in 
  let 'Clist ((tail_1223, next_idxs_1224)) :=
    x_1220 in 
  (if ((array_index (tail_1223) (@cast _ uint32 _ (rq_1222))) =.? (
        sentinel_v)):bool then (@None int8) else (@Some int8 (array_index (
          next_idxs_1224) (@cast _ uint32 _ (array_index (tail_1223) (
              @cast _ uint32 _ (rq_1222))))))).


Definition clist_advance
  (x_1225 : clist_t)
  (rq_1226 : runqueue_id_t)
  
  : clist_t :=
  let 'RunqueueId (rq_1227) :=
    rq_1226 in 
  let 'Clist ((tail_1228, next_idxs_1229)) :=
    x_1225 in 
  let '(tail_1228) :=
    if (array_index (tail_1228) (@cast _ uint32 _ (rq_1227))) !=.? (
      sentinel_v):bool then (let tail_1228 :=
        array_upd tail_1228 (@cast _ uint32 _ (rq_1227)) (array_index (
            next_idxs_1229) (@cast _ uint32 _ (array_index (tail_1228) (
                @cast _ uint32 _ (rq_1227))))) in 
      (tail_1228)) else ((tail_1228)) in 
  Clist ((tail_1228, next_idxs_1229)).


Inductive run_queue_t :=
| RunQueue : (int32 '× clist_t) -> run_queue_t.

Definition runqueue_new   : run_queue_t :=
  RunQueue ((@repr WORDSIZE32 (0), clist_new )).


Definition runqueue_add
  (y_1230 : run_queue_t)
  (n_1231 : thread_id_t)
  (rq_1232 : runqueue_id_t)
  
  : run_queue_t :=
  let 'RunqueueId (rq_u8_1233) :=
    rq_1232 in 
  let 'RunQueue ((bitcache_1234, queues_1235)) :=
    y_1230 in 
  let bitcache_1234 :=
    (bitcache_1234) .| ((@repr WORDSIZE32 (1)) shift_left (@cast _ uint32 _ (
          rq_u8_1233))) in 
  let queues_1235 :=
    clist_push (queues_1235) (n_1231) (rq_1232) in 
  RunQueue ((bitcache_1234, queues_1235)).


Definition runqueue_del
  (y_1236 : run_queue_t)
  (n_1237 : thread_id_t)
  (rq_1238 : runqueue_id_t)
  
  : run_queue_t :=
  let 'RunqueueId (rq_u8_1239) :=
    rq_1238 in 
  let 'RunQueue ((bitcache_1240, queues_1241)) :=
    y_1236 in 
  let '(queues_1242, popped_1243) :=
    clist_pop_head (queues_1241) (rq_1238) in 
  let '(bitcache_1240) :=
    if clist_is_empty (queues_1242) (rq_1238):bool then (let bitcache_1240 :=
        (bitcache_1240) .& (not ((@repr WORDSIZE32 (1)) shift_left (
              @cast _ uint32 _ (rq_u8_1239)))) in 
      (bitcache_1240)) else ((bitcache_1240)) in 
  RunQueue ((bitcache_1240, queues_1242)).


Definition runqueue_ffs (val_1244 : int32)  : int32 :=
  (pub_u32 (uint32_bits_v)) .- (pub_uint32_leading_zeros (val_1244)).


Definition runqueue_get_next (y_1245 : run_queue_t)  : (option int8) :=
  let 'RunQueue ((bitcache_1246, queues_1247)) :=
    y_1245 in 
  let rq_ffs_1248 : int32 :=
    runqueue_ffs ((bitcache_1246)) in 
  let out_1249 : (option int8) :=
    @None int8 in 
  let '(out_1249) :=
    if (rq_ffs_1248) >.? (@repr WORDSIZE32 (0)):bool then (
      let rq_1250 : runqueue_id_t :=
        RunqueueId (@cast _ uint8 _ ((rq_ffs_1248) .- (
              @repr WORDSIZE32 (1)))) in 
      let out_1249 :=
        clist_peek_head (queues_1247) (rq_1250) in 
      (out_1249)) else ((out_1249)) in 
  out_1249.


Definition runqueue_advance
  (y_1251 : run_queue_t)
  (rq_1252 : runqueue_id_t)
  
  : run_queue_t :=
  let 'RunQueue ((bitcache_1253, queues_1254)) :=
    y_1251 in 
  let queues_1254 :=
    clist_advance (queues_1254) (rq_1252) in 
  RunQueue ((bitcache_1253, queues_1254)).


