module Hpack.Huffman.Refine.DfaTable

/// Interface for the generated DFA transition table's correctness proof.
///
/// Exposed: the transparent *accessors* a consumer needs to read a packed cell and
/// name a state (`state_of`, `cell_next`, `cell_emit`, the chunk selector
/// `dfa_chunk_list`), and the two headline facts — every cell equals the spec
/// `step` (`chunk_table_ok`) and every accept flag equals `is_accepting`
/// (`table_accept_ok`). Sealed in the `.fst`: the normaliser-fast restatement
/// (`find_l`/`lookup_fast`/`step_fast` and their `*_eq` correctness lemmas) and the
/// bulk `assert_norm` machinery (`check_all`/`check_acc` + their `*_holds`/`*_index`
/// walkers). A consumer (the loop in `Lowstar.Dfa`) sees only "this cell is the
/// spec step", never the 4 K-cell normalisation that proves it.

open Hpack.Huffman.Table
open Hpack.Huffman.Spec.Codec
open Hpack.Huffman.Spec.Dfa
open Hpack.Huffman.Lowstar.DfaTables
open FStar.Mul
open FStar.List.Tot
module L = FStar.List.Tot
module Seq = FStar.Seq
module U8 = FStar.UInt8
module U32 = FStar.UInt32

/// The state at id `i`; the out-of-range id `dfa_n_states` is the fail state.
let state_of (i:nat) : dstate =
  if i >= dfa_n_states then DFail
  else (let k = L.index dfa_state_keys i in DLive (k / 32) (k % 32))

/// A cell packs `next_id*65536 + emit_flag*256 + sym` (see `Lowstar.DfaTables`).
let cell_next (c:U32.t) : nat = U32.v c / 65536
let cell_emit (c:U32.t) : list byte =
  if (U32.v c / 256) % 256 = 1 then [U32.v c % 256] else []

/// Chunk `k`'s cell list (the 16-way selector the proof ranges over).
let dfa_chunk_list (k:nat{k < dfa_n_chunks}) : (l:list U32.t{L.length l == dfa_chunk_size}) =
  match k with
  | 0  -> dfa_chunk_0_list  | 1  -> dfa_chunk_1_list  | 2  -> dfa_chunk_2_list
  | 3  -> dfa_chunk_3_list  | 4  -> dfa_chunk_4_list  | 5  -> dfa_chunk_5_list
  | 6  -> dfa_chunk_6_list  | 7  -> dfa_chunk_7_list  | 8  -> dfa_chunk_8_list
  | 9  -> dfa_chunk_9_list  | 10 -> dfa_chunk_10_list | 11 -> dfa_chunk_11_list
  | 12 -> dfa_chunk_12_list | 13 -> dfa_chunk_13_list | 14 -> dfa_chunk_14_list
  | _  -> dfa_chunk_15_list

/// Chunk `k`, offset `off` of the table agrees with the spec `step`: in terms of
/// the flat position `p = chunk_size*k + off`, its next-id names step's next state
/// and its emit is step's output. (`Lowstar.Dfa.read_cell` reads `dfa_chunks[k][off]`
/// and applies this.)
val chunk_table_ok (k:nat{k < dfa_n_chunks}) (off:nat{off < dfa_chunk_size})
  : Lemma (let c = L.index (dfa_chunk_list k) off in
           let p = dfa_chunk_size * k + off in
           cell_next c <= dfa_n_states /\
           state_of (cell_next c) == fst (step (state_of (p / 16)) (p % 16)) /\
           cell_emit c == snd (step (state_of (p / 16)) (p % 16)))

/// The per-state accept flag matches spec acceptance.
val table_accept_ok (i:nat{i < dfa_n_states})
  : Lemma (U8.v (Seq.index dfa_accept_contents i)
           = (if is_accepting (state_of i) then 1 else 0))
