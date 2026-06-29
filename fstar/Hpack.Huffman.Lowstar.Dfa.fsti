module Hpack.Huffman.Lowstar.Dfa

/// Interface for the table-driven (nibble DFA) decoder's executable access layer.
/// The loop builds ONLY on this — it never sees the ~4 K-cell generated table, the
/// 16-way chunk dispatch, or the table-correctness proof, all sealed in the `.fst`.
/// Exposed: the two byte<->nibble bit-view lemmas, and the two executable reads
/// (`read_cell`, `accept_at`), each carrying its spec-step contract.

open FStar.HyperStack.ST
open FStar.Mul
open Hpack.Huffman.Lowstar.DfaTables
module Seq = FStar.Seq
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module I32 = FStar.Int32
module B = LowStar.Buffer
module L = FStar.List.Tot
module SC = Hpack.Huffman.Spec.Codec
module SD = Hpack.Huffman.Spec.Decode
module SDfa = Hpack.Huffman.Spec.Dfa
module RD = Hpack.Huffman.Bridge.Decode
module RDT = Hpack.Huffman.Refine.DfaTable

/// High nibble: `nibble_bits (byte/16)` are the four MSB-first bits at `8*i..+3`.
val nibble_hi (s:Seq.seq U8.t) (i:nat{i < Seq.length s})
  : Lemma (SDfa.nibble_bits (U8.v (Seq.index s i) / 16) ==
           [SD.bit_at s (8 * i); SD.bit_at s (8 * i + 1);
            SD.bit_at s (8 * i + 2); SD.bit_at s (8 * i + 3)])

/// Low nibble: `nibble_bits (byte%16)` are the four MSB-first bits at `8*i+4..+7`.
val nibble_lo (s:Seq.seq U8.t) (i:nat{i < Seq.length s})
  : Lemma (SDfa.nibble_bits (U8.v (Seq.index s i) % 16) ==
           [SD.bit_at s (8 * i + 4); SD.bit_at s (8 * i + 5);
            SD.bit_at s (8 * i + 6); SD.bit_at s (8 * i + 7)])

/// The cell `c` read for state `cur`, nibble `nib` agrees with the spec step:
/// its next-id names the step's next state, and its emit is the step's output.
unfold let cell_ok_post (cur:U32.t) (nib:U32.t{U32.v nib < 16}) (c:U32.t) : prop =
  RDT.cell_next c <= dfa_n_states /\
  RDT.state_of (RDT.cell_next c) == fst (SDfa.step (RDT.state_of (U32.v cur)) (U32.v nib)) /\
  RDT.cell_emit c == snd (SDfa.step (RDT.state_of (U32.v cur)) (U32.v nib))

/// Read the transition cell for state `cur`, nibble `nib` (flat position
/// `cur*16 + nib`). Memory-safe, heap-preserving; satisfies `cell_ok_post`.
val read_cell (cur:U32.t{U32.v cur < dfa_n_states}) (nib:U32.t{U32.v nib < 16})
  : Stack U32.t (requires fun _ -> True)
                (ensures fun h0 c h1 -> h0 == h1 /\ cell_ok_post cur nib c)

/// Is state `cur` a valid stopping point (the spec's `is_accepting`)?
val accept_at (cur:U32.t{U32.v cur < dfa_n_states})
  : Stack bool (requires fun _ -> True)
    (ensures fun h0 b h1 -> h0 == h1 /\ b == SDfa.is_accepting (RDT.state_of (U32.v cur)))

/// Huffman-decode `src[0..src_len)` into `dst` via the nibble DFA, writing the
/// decoded byte count to `out_len[0]` (returns 0 on success, -1 on error). Same
/// contract as the per-bit `Lowstar.Codec.decode` (Some-direction): a drop-in
/// replacement, so the end-to-end round-trip carries over to D6's facade swap.
val decode_dfa
  (src:B.buffer U8.t) (src_len:U32.t)
  (dst:B.buffer U8.t) (dst_cap:U32.t)
  (out_len:B.buffer U32.t)
  : Stack I32.t
    (requires fun h ->
      B.live h src /\ B.live h dst /\ B.live h out_len /\
      B.loc_disjoint (B.loc_buffer dst) (B.loc_buffer src) /\
      B.loc_disjoint (B.loc_buffer dst) (B.loc_buffer out_len) /\
      B.loc_disjoint (B.loc_buffer out_len) (B.loc_buffer src) /\
      B.length src == U32.v src_len /\ U32.v dst_cap <= B.length dst /\
      B.length out_len == 1 /\ U32.v src_len < pow2 27)
    (ensures fun h0 r h1 ->
      B.modifies (B.loc_union (B.loc_buffer dst) (B.loc_buffer out_len)) h0 h1 /\
      U32.v (Seq.index (B.as_seq h1 out_len) 0) <= U32.v dst_cap /\
      (let spec = SC.decode_bits (SD.bytes_to_bits (B.as_seq h0 src)) in
       ((Some? spec /\ L.length (Some?.v spec) <= U32.v dst_cap) ==>
         (r == 0l /\
          U32.v (Seq.index (B.as_seq h1 out_len) 0) == L.length (Some?.v spec) /\
          RD.decoded_prefix (B.as_seq h1 dst) (U32.v (Seq.index (B.as_seq h1 out_len) 0))
            == Some?.v spec)) /\
       (* rejection-completeness (None-direction): every stream the RFC
          spec rejects makes the extracted decoder return -1. *)
       (None? spec ==> r == (-1l))))
