module Hpack.Huffman.Lowstar.Dfa

/// The executable table-driven (nibble DFA) Huffman decoder, lowered to C.
///
/// The loop keeps a single state id `cur` (vs the per-bit decoder's `(acc,
/// nbits)`), and per nibble does ONE table lookup — `dfa_chunks[cur*16+nibble /
/// chunk_size][...]` — advancing four input bits at a time. Correctness is the
/// `decode_go` simulation again (so the shipped `decode`'s `ensures` and the
/// end-to-end round-trip carry over unchanged), routed through the automaton:
/// `Refine.DfaTable.chunk_table_ok` (the cell equals the spec step) and
/// `Refine.Dfa.decode_go_nibble` (one step advances `decode_go` by four bits).
///
/// This file begins with the byte<->nibble bit-view lemmas: a nibble read from a
/// byte (`byte/16` high, `byte%16` low) has `nibble_bits` equal to the four
/// `Spec.Decode.bit_at` bits the per-bit decoder would read at that position.

open FStar.Mul
open FStar.List.Tot
module Seq = FStar.Seq
module U8 = FStar.UInt8
module L = FStar.List.Tot
module M = FStar.Math.Lemmas
module SD = Hpack.Huffman.Spec.Decode
module SDfa = Hpack.Huffman.Spec.Dfa

open FStar.HyperStack.ST
open Hpack.Huffman.Lowstar.DfaTables
module IB = LowStar.ImmutableBuffer
module B = LowStar.Buffer
module U32 = FStar.UInt32
module I32 = FStar.Int32
module G = FStar.Ghost
module Cast = FStar.Int.Cast
module SC = Hpack.Huffman.Spec.Codec
module RD = Hpack.Huffman.Bridge.Decode
module RDfa = Hpack.Huffman.Spec.DfaEquiv
module RDT = Hpack.Huffman.Refine.DfaTable

#set-options "--fuel 1 --ifuel 1 --z3rlimit 60"

/// `(8*i+j)/8 == i` and `(8*i+j)%8 == j` for `j < 8` (the bit at global index
/// `8*i+j` lives in byte `i` at in-byte offset `j`).
let idx88 (i:nat) (j:nat{j < 8}) : Lemma ((8 * i + j) / 8 == i /\ (8 * i + j) % 8 == j)
  = M.lemma_div_plus j i 8;
    M.lemma_mod_plus j i 8

/// High nibble: `nibble_bits (byte/16)` are the four MSB-first bits at `8*i..+3`.
let nibble_hi (s:Seq.seq U8.t) (i:nat{i < Seq.length s})
  : Lemma (SDfa.nibble_bits (U8.v (Seq.index s i) / 16) ==
           [SD.bit_at s (8 * i); SD.bit_at s (8 * i + 1);
            SD.bit_at s (8 * i + 2); SD.bit_at s (8 * i + 3)])
  = let b = U8.v (Seq.index s i) in
    assert_norm (pow2 7 == 128); assert_norm (pow2 6 == 64);
    assert_norm (pow2 5 == 32);  assert_norm (pow2 4 == 16);
    M.division_multiplication_lemma b 16 8;   // b/16/8 == b/128
    M.division_multiplication_lemma b 16 4;   // b/16/4 == b/64
    M.division_multiplication_lemma b 16 2;   // b/16/2 == b/32
    idx88 i 0; idx88 i 1; idx88 i 2; idx88 i 3

/// Bit `k < 4` of `byte%16` equals bit `k` of `byte` (low nibble = low 4 bits).
let lo_bit (b:nat) (k:nat{k < 4}) : Lemma ((b % 16 / pow2 k) % 2 == (b / pow2 k) % 2)
  = assert_norm (pow2 4 == 16);
    M.pow2_modulo_division_lemma_1 b k 4;     // (b % pow2 4)/pow2 k == (b/pow2 k) % pow2 (4-k)
    M.pow2_double_mult (4 - k - 1);           // pow2 (4-k) == 2 * pow2 (4-k-1)
    M.modulo_modulo_lemma (b / pow2 k) 2 (pow2 (4 - k - 1))   // (x % (2*m)) % 2 == x % 2

/// Low nibble: `nibble_bits (byte%16)` are the four MSB-first bits at `8*i+4..+7`.
let nibble_lo (s:Seq.seq U8.t) (i:nat{i < Seq.length s})
  : Lemma (SDfa.nibble_bits (U8.v (Seq.index s i) % 16) ==
           [SD.bit_at s (8 * i + 4); SD.bit_at s (8 * i + 5);
            SD.bit_at s (8 * i + 6); SD.bit_at s (8 * i + 7)])
  = let b = U8.v (Seq.index s i) in
    assert_norm (pow2 3 == 8); assert_norm (pow2 2 == 4);
    assert_norm (pow2 1 == 2); assert_norm (pow2 0 == 1);
    lo_bit b 3; lo_bit b 2; lo_bit b 1; lo_bit b 0;
    idx88 i 4; idx88 i 5; idx88 i 6; idx88 i 7

(* ---------------------------------------------------------------------- *)
(* Reading a transition cell (16-way chunk switch -> C jump table)          *)
(* ---------------------------------------------------------------------- *)

/// Generic chunk read, verified ONCE (not per branch): recall a recallable
/// immutable buffer's witnessed contents and index it. Isolating this keeps the
/// 256-element `seq_of_list` recall out of `read_cell`'s 16-way VC (inlining it
/// per branch made that VC superlinear).
/// `inline_for_extraction` so the spec-only `cl` (used only in the erased
/// `recall_contents`/`lemma_seq_of_list_index`) does not survive as a runtime
/// parameter — otherwise each `read_chunk_K` call site would pass the `noextract`
/// `dfa_chunk_K_list`, which KaRaMeL rejects as having no C implementation. After
/// inlining + erasure each `read_chunk_K` is just an `IB.index` of its buffer.
#push-options "--fuel 0 --ifuel 1 --z3rlimit 30"
inline_for_extraction
let read_at (b:IB.ibuffer U32.t) (cl:list U32.t{L.length cl == dfa_chunk_size})
  (off:U32.t{U32.v off < dfa_chunk_size})
  : Stack U32.t
    (requires fun _ -> IB.recallable b /\ IB.witnessed b (IB.cpred (Seq.seq_of_list cl)))
    (ensures fun h0 c h1 -> h0 == h1 /\ c == L.index cl (U32.v off))
  = IB.recall_contents b (Seq.seq_of_list cl);
    Seq.lemma_seq_of_list_index cl (U32.v off);
    IB.index b off
#pop-options

/// One standalone read per chunk — each its OWN verification condition. Inlining
/// all 16 into `read_cell`'s body made that single VC superlinear (>150 s); as
/// separate functions each is ~3 s and the total is linear. `read_chunk K`
/// requires that `cur,nib` actually land in chunk `K` (`p/256 == K`); the chunk
/// offset is `p % 256`, and `chunk_table_ok` ties the read cell to the spec step.
#push-options "--fuel 0 --ifuel 1 --z3rlimit 50"
let read_chunk_arith (cur:U32.t{U32.v cur < dfa_n_states}) (nib:U32.t{U32.v nib < 16})
  : Lemma (let p = U32.v cur * 16 + U32.v nib in p / 16 == U32.v cur /\ p % 16 == U32.v nib)
  = M.lemma_div_plus (U32.v nib) (U32.v cur) 16;
    M.lemma_mod_plus (U32.v nib) (U32.v cur) 16
#pop-options

#push-options "--fuel 0 --ifuel 1 --z3rlimit 60"
private let read_chunk_0 (cur:U32.t{U32.v cur < dfa_n_states}) (nib:U32.t{U32.v nib < 16})
  : Stack U32.t (requires fun _ -> (U32.v cur * 16 + U32.v nib) / 256 == 0)
                (ensures fun h0 c h1 -> h0 == h1 /\ cell_ok_post cur nib c)
  = let p = U32.add (U32.mul cur 16ul) nib in let off = U32.rem p 256ul in
    M.lemma_div_mod (U32.v p) 256; read_chunk_arith cur nib;
    let c = read_at dfa_chunk_0 dfa_chunk_0_list off in RDT.chunk_table_ok 0 (U32.v off); c
private let read_chunk_1 (cur:U32.t{U32.v cur < dfa_n_states}) (nib:U32.t{U32.v nib < 16})
  : Stack U32.t (requires fun _ -> (U32.v cur * 16 + U32.v nib) / 256 == 1)
                (ensures fun h0 c h1 -> h0 == h1 /\ cell_ok_post cur nib c)
  = let p = U32.add (U32.mul cur 16ul) nib in let off = U32.rem p 256ul in
    M.lemma_div_mod (U32.v p) 256; read_chunk_arith cur nib;
    let c = read_at dfa_chunk_1 dfa_chunk_1_list off in RDT.chunk_table_ok 1 (U32.v off); c
private let read_chunk_2 (cur:U32.t{U32.v cur < dfa_n_states}) (nib:U32.t{U32.v nib < 16})
  : Stack U32.t (requires fun _ -> (U32.v cur * 16 + U32.v nib) / 256 == 2)
                (ensures fun h0 c h1 -> h0 == h1 /\ cell_ok_post cur nib c)
  = let p = U32.add (U32.mul cur 16ul) nib in let off = U32.rem p 256ul in
    M.lemma_div_mod (U32.v p) 256; read_chunk_arith cur nib;
    let c = read_at dfa_chunk_2 dfa_chunk_2_list off in RDT.chunk_table_ok 2 (U32.v off); c
private let read_chunk_3 (cur:U32.t{U32.v cur < dfa_n_states}) (nib:U32.t{U32.v nib < 16})
  : Stack U32.t (requires fun _ -> (U32.v cur * 16 + U32.v nib) / 256 == 3)
                (ensures fun h0 c h1 -> h0 == h1 /\ cell_ok_post cur nib c)
  = let p = U32.add (U32.mul cur 16ul) nib in let off = U32.rem p 256ul in
    M.lemma_div_mod (U32.v p) 256; read_chunk_arith cur nib;
    let c = read_at dfa_chunk_3 dfa_chunk_3_list off in RDT.chunk_table_ok 3 (U32.v off); c
private let read_chunk_4 (cur:U32.t{U32.v cur < dfa_n_states}) (nib:U32.t{U32.v nib < 16})
  : Stack U32.t (requires fun _ -> (U32.v cur * 16 + U32.v nib) / 256 == 4)
                (ensures fun h0 c h1 -> h0 == h1 /\ cell_ok_post cur nib c)
  = let p = U32.add (U32.mul cur 16ul) nib in let off = U32.rem p 256ul in
    M.lemma_div_mod (U32.v p) 256; read_chunk_arith cur nib;
    let c = read_at dfa_chunk_4 dfa_chunk_4_list off in RDT.chunk_table_ok 4 (U32.v off); c
private let read_chunk_5 (cur:U32.t{U32.v cur < dfa_n_states}) (nib:U32.t{U32.v nib < 16})
  : Stack U32.t (requires fun _ -> (U32.v cur * 16 + U32.v nib) / 256 == 5)
                (ensures fun h0 c h1 -> h0 == h1 /\ cell_ok_post cur nib c)
  = let p = U32.add (U32.mul cur 16ul) nib in let off = U32.rem p 256ul in
    M.lemma_div_mod (U32.v p) 256; read_chunk_arith cur nib;
    let c = read_at dfa_chunk_5 dfa_chunk_5_list off in RDT.chunk_table_ok 5 (U32.v off); c
private let read_chunk_6 (cur:U32.t{U32.v cur < dfa_n_states}) (nib:U32.t{U32.v nib < 16})
  : Stack U32.t (requires fun _ -> (U32.v cur * 16 + U32.v nib) / 256 == 6)
                (ensures fun h0 c h1 -> h0 == h1 /\ cell_ok_post cur nib c)
  = let p = U32.add (U32.mul cur 16ul) nib in let off = U32.rem p 256ul in
    M.lemma_div_mod (U32.v p) 256; read_chunk_arith cur nib;
    let c = read_at dfa_chunk_6 dfa_chunk_6_list off in RDT.chunk_table_ok 6 (U32.v off); c
private let read_chunk_7 (cur:U32.t{U32.v cur < dfa_n_states}) (nib:U32.t{U32.v nib < 16})
  : Stack U32.t (requires fun _ -> (U32.v cur * 16 + U32.v nib) / 256 == 7)
                (ensures fun h0 c h1 -> h0 == h1 /\ cell_ok_post cur nib c)
  = let p = U32.add (U32.mul cur 16ul) nib in let off = U32.rem p 256ul in
    M.lemma_div_mod (U32.v p) 256; read_chunk_arith cur nib;
    let c = read_at dfa_chunk_7 dfa_chunk_7_list off in RDT.chunk_table_ok 7 (U32.v off); c
private let read_chunk_8 (cur:U32.t{U32.v cur < dfa_n_states}) (nib:U32.t{U32.v nib < 16})
  : Stack U32.t (requires fun _ -> (U32.v cur * 16 + U32.v nib) / 256 == 8)
                (ensures fun h0 c h1 -> h0 == h1 /\ cell_ok_post cur nib c)
  = let p = U32.add (U32.mul cur 16ul) nib in let off = U32.rem p 256ul in
    M.lemma_div_mod (U32.v p) 256; read_chunk_arith cur nib;
    let c = read_at dfa_chunk_8 dfa_chunk_8_list off in RDT.chunk_table_ok 8 (U32.v off); c
private let read_chunk_9 (cur:U32.t{U32.v cur < dfa_n_states}) (nib:U32.t{U32.v nib < 16})
  : Stack U32.t (requires fun _ -> (U32.v cur * 16 + U32.v nib) / 256 == 9)
                (ensures fun h0 c h1 -> h0 == h1 /\ cell_ok_post cur nib c)
  = let p = U32.add (U32.mul cur 16ul) nib in let off = U32.rem p 256ul in
    M.lemma_div_mod (U32.v p) 256; read_chunk_arith cur nib;
    let c = read_at dfa_chunk_9 dfa_chunk_9_list off in RDT.chunk_table_ok 9 (U32.v off); c
private let read_chunk_10 (cur:U32.t{U32.v cur < dfa_n_states}) (nib:U32.t{U32.v nib < 16})
  : Stack U32.t (requires fun _ -> (U32.v cur * 16 + U32.v nib) / 256 == 10)
                (ensures fun h0 c h1 -> h0 == h1 /\ cell_ok_post cur nib c)
  = let p = U32.add (U32.mul cur 16ul) nib in let off = U32.rem p 256ul in
    M.lemma_div_mod (U32.v p) 256; read_chunk_arith cur nib;
    let c = read_at dfa_chunk_10 dfa_chunk_10_list off in RDT.chunk_table_ok 10 (U32.v off); c
private let read_chunk_11 (cur:U32.t{U32.v cur < dfa_n_states}) (nib:U32.t{U32.v nib < 16})
  : Stack U32.t (requires fun _ -> (U32.v cur * 16 + U32.v nib) / 256 == 11)
                (ensures fun h0 c h1 -> h0 == h1 /\ cell_ok_post cur nib c)
  = let p = U32.add (U32.mul cur 16ul) nib in let off = U32.rem p 256ul in
    M.lemma_div_mod (U32.v p) 256; read_chunk_arith cur nib;
    let c = read_at dfa_chunk_11 dfa_chunk_11_list off in RDT.chunk_table_ok 11 (U32.v off); c
private let read_chunk_12 (cur:U32.t{U32.v cur < dfa_n_states}) (nib:U32.t{U32.v nib < 16})
  : Stack U32.t (requires fun _ -> (U32.v cur * 16 + U32.v nib) / 256 == 12)
                (ensures fun h0 c h1 -> h0 == h1 /\ cell_ok_post cur nib c)
  = let p = U32.add (U32.mul cur 16ul) nib in let off = U32.rem p 256ul in
    M.lemma_div_mod (U32.v p) 256; read_chunk_arith cur nib;
    let c = read_at dfa_chunk_12 dfa_chunk_12_list off in RDT.chunk_table_ok 12 (U32.v off); c
private let read_chunk_13 (cur:U32.t{U32.v cur < dfa_n_states}) (nib:U32.t{U32.v nib < 16})
  : Stack U32.t (requires fun _ -> (U32.v cur * 16 + U32.v nib) / 256 == 13)
                (ensures fun h0 c h1 -> h0 == h1 /\ cell_ok_post cur nib c)
  = let p = U32.add (U32.mul cur 16ul) nib in let off = U32.rem p 256ul in
    M.lemma_div_mod (U32.v p) 256; read_chunk_arith cur nib;
    let c = read_at dfa_chunk_13 dfa_chunk_13_list off in RDT.chunk_table_ok 13 (U32.v off); c
private let read_chunk_14 (cur:U32.t{U32.v cur < dfa_n_states}) (nib:U32.t{U32.v nib < 16})
  : Stack U32.t (requires fun _ -> (U32.v cur * 16 + U32.v nib) / 256 == 14)
                (ensures fun h0 c h1 -> h0 == h1 /\ cell_ok_post cur nib c)
  = let p = U32.add (U32.mul cur 16ul) nib in let off = U32.rem p 256ul in
    M.lemma_div_mod (U32.v p) 256; read_chunk_arith cur nib;
    let c = read_at dfa_chunk_14 dfa_chunk_14_list off in RDT.chunk_table_ok 14 (U32.v off); c
private let read_chunk_15 (cur:U32.t{U32.v cur < dfa_n_states}) (nib:U32.t{U32.v nib < 16})
  : Stack U32.t (requires fun _ -> (U32.v cur * 16 + U32.v nib) / 256 == 15)
                (ensures fun h0 c h1 -> h0 == h1 /\ cell_ok_post cur nib c)
  = let p = U32.add (U32.mul cur 16ul) nib in let off = U32.rem p 256ul in
    M.lemma_div_mod (U32.v p) 256; read_chunk_arith cur nib;
    let c = read_at dfa_chunk_15 dfa_chunk_15_list off in RDT.chunk_table_ok 15 (U32.v off); c
#pop-options

/// Read the table cell for state `cur`, nibble `nib`. The 16-way `match` on the
/// chunk id `p / 256` extracts to a C `switch` (jump table); each arm forwards to
/// a standalone `read_chunk_K`, so this dispatcher's own VC is trivial.
#push-options "--fuel 0 --ifuel 1 --z3rlimit 30"
let read_cell (cur:U32.t{U32.v cur < dfa_n_states}) (nib:U32.t{U32.v nib < 16})
  : Stack U32.t (requires fun _ -> True) (ensures fun h0 c h1 -> h0 == h1 /\ cell_ok_post cur nib c)
  = let k = U32.div (U32.add (U32.mul cur 16ul) nib) 256ul in
    match k with
    | 0ul  -> read_chunk_0  cur nib | 1ul  -> read_chunk_1  cur nib
    | 2ul  -> read_chunk_2  cur nib | 3ul  -> read_chunk_3  cur nib
    | 4ul  -> read_chunk_4  cur nib | 5ul  -> read_chunk_5  cur nib
    | 6ul  -> read_chunk_6  cur nib | 7ul  -> read_chunk_7  cur nib
    | 8ul  -> read_chunk_8  cur nib | 9ul  -> read_chunk_9  cur nib
    | 10ul -> read_chunk_10 cur nib | 11ul -> read_chunk_11 cur nib
    | 12ul -> read_chunk_12 cur nib | 13ul -> read_chunk_13 cur nib
    | 14ul -> read_chunk_14 cur nib | _    -> read_chunk_15 cur nib
#pop-options

(* ---------------------------------------------------------------------- *)
(* Reading the per-state accept flag                                        *)
(* ---------------------------------------------------------------------- *)

#push-options "--fuel 0 --ifuel 1 --z3rlimit 40"
/// Is state `cur` a valid stopping point? Reads `dfa_accept[cur]`; correctness via
/// `table_accept_ok` (the flag equals the spec's `is_accepting`).
let accept_at (cur:U32.t{U32.v cur < dfa_n_states})
  : Stack bool (requires fun _ -> True)
    (ensures fun h0 b h1 -> h0 == h1 /\ b == SDfa.is_accepting (RDT.state_of (U32.v cur)))
  = IB.recall_contents dfa_accept dfa_accept_contents;
    Seq.lemma_seq_of_list_index dfa_accept_list (U32.v cur);
    RDT.table_accept_ok (U32.v cur);
    let v = IB.index dfa_accept cur in
    U8.eq v 1uy
#pop-options

/// `[x0;x1;x2;x3] @ rest == x0::x1::x2::x3::rest` (the loop runs at `--fuel 0`,
/// where `L.append` over the 4-element nibble list won't unfold on its own).
let append4 (#a:Type) (x0 x1 x2 x3:a) (rest:list a)
  : Lemma ([x0; x1; x2; x3] `L.append` rest == x0 :: x1 :: x2 :: x3 :: rest)
  = assert_norm ([x0; x1; x2; x3] `L.append` rest == x0 :: x1 :: x2 :: x3 :: rest)

/// The four bits of the nibble at byte `i`, in-byte offset `biti` (0 = high,
/// 4 = low), are exactly `bit_at` at `8*i+biti .. +3`. Case-split internally so
/// the caller need not (the loop reads `nib` and `biti` as runtime values).
#push-options "--fuel 0 --ifuel 1 --z3rlimit 40"
let nibble_relate (s:Seq.seq U8.t) (i:nat{i < Seq.length s})
  (biti:nat{biti == 0 \/ biti == 4}) (nibv:nat)
  : Lemma (requires (biti == 0 ==> nibv == U8.v (Seq.index s i) / 16) /\
                    (biti == 4 ==> nibv == U8.v (Seq.index s i) % 16))
          (ensures SDfa.nibble_bits nibv ==
                   [SD.bit_at s (8 * i + biti); SD.bit_at s (8 * i + biti + 1);
                    SD.bit_at s (8 * i + biti + 2); SD.bit_at s (8 * i + biti + 3)])
  = if biti = 0 then nibble_hi s i else nibble_lo s i
#pop-options

(* ---------------------------------------------------------------------- *)
(* The nibble decode loop (simulates Spec.Codec.decode_go, 4 bits/step)     *)
(* ---------------------------------------------------------------------- *)

#push-options "--fuel 0 --ifuel 2 --z3rlimit 150"
/// Decode from bit position `g` (a multiple of 4) with the automaton in state
/// `cur` (whose spec state is `DLive gacc gnbits`), having already written
/// `written` bytes (= `gout`). Mirrors `Lowstar.Codec.decode_loop` but advances
/// one nibble per step via a single `read_cell`. Some-direction simulation.
let rec dfa_loop
  (src dst:B.buffer U8.t) (src_len dst_cap g cur written:U32.t)
  (gsrc:G.erased (Seq.seq U8.t)) (gout:G.erased (list SC.byte)) (gacc gnbits:G.erased nat)
  (out_len:B.buffer U32.t)
  : Stack I32.t
    (requires fun h ->
      B.live h src /\ B.live h dst /\ B.live h out_len /\
      B.loc_disjoint (B.loc_buffer dst) (B.loc_buffer src) /\
      B.loc_disjoint (B.loc_buffer dst) (B.loc_buffer out_len) /\
      B.loc_disjoint (B.loc_buffer out_len) (B.loc_buffer src) /\
      B.length src == U32.v src_len /\ U32.v dst_cap <= B.length dst /\ B.length out_len == 1 /\
      U32.v src_len < pow2 27 /\
      U32.v g <= 8 * U32.v src_len /\ U32.v g % 4 == 0 /\
      U32.v cur < dfa_n_states /\ U32.v written <= U32.v dst_cap /\
      RDT.state_of (U32.v cur) == SDfa.DLive (G.reveal gacc) (G.reveal gnbits) /\
      G.reveal gsrc == B.as_seq h src /\
      G.reveal gout == RD.decoded_prefix (B.as_seq h dst) (U32.v written))
    (ensures fun h0 r h1 ->
      B.modifies (B.loc_union (B.loc_buffer dst) (B.loc_buffer out_len)) h0 h1 /\
      B.live h1 dst /\ B.live h1 out_len /\
      U32.v (Seq.index (B.as_seq h1 out_len) 0) <= U32.v dst_cap /\
      (let spec = SC.decode_go (SD.bits_from (G.reveal gsrc) (U32.v g))
                               (G.reveal gacc) (G.reveal gnbits) (G.reveal gout) in
       ((Some? spec /\ L.length (Some?.v spec) <= U32.v dst_cap) ==>
         (r == 0l /\
          U32.v (Seq.index (B.as_seq h1 out_len) 0) == L.length (Some?.v spec) /\
          RD.decoded_prefix (B.as_seq h1 dst) (U32.v (Seq.index (B.as_seq h1 out_len) 0))
            == Some?.v spec)) /\
       (* rejection-completeness (None-direction): the spec rejecting the
          remaining stream forces the loop to report failure. *)
       (None? spec ==> r == (-1l))))
    (decreases (8 * U32.v src_len - U32.v g))
  = let h0 = get () in
    RD.decoded_prefix_length (B.as_seq h0 dst) (U32.v written);
    assert_norm (pow2 27 == 134217728); assert_norm (pow2 32 == 4294967296);
    let nbit_total = U32.mul 8ul src_len in
    if U32.eq g nbit_total then begin
      (* end of input: bits_from is empty; spec = valid_padding ? Some gout : None,
         and is_accepting (state_of cur) == valid_padding_v gacc gnbits *)
      SD.bits_from_nil (G.reveal gsrc) (U32.v g);
      RD.decode_go_nil (G.reveal gacc) (G.reveal gnbits) (G.reveal gout);
      B.upd out_len 0ul written;
      let ok = accept_at cur in
      if ok then 0l else (-1l)
    end else begin
      let bytei = U32.div g 8ul in
      let biti  = U32.rem g 8ul in
      M.lemma_div_mod (U32.v g) 8;                 (* g = 8*bytei + biti, biti in {0,4} *)
      let bx = B.index src bytei in
      let nib = if U32.eq biti 0ul then Cast.uint8_to_uint32 (U8.div bx 16uy)
                                   else Cast.uint8_to_uint32 (U8.rem bx 16uy) in
      (* the nibble's four bits are exactly bits_from at g..g+3 *)
      M.modulo_modulo_lemma (U32.v g) 4 2;         (* (g%8)%4 == g%4 == 0, so biti in {0,4} *)
      nibble_relate (G.reveal gsrc) (U32.v bytei) (U32.v biti) (U32.v nib);
      SD.bits_from_unfold (G.reveal gsrc) (U32.v g);
      SD.bits_from_unfold (G.reveal gsrc) (U32.v g + 1);
      SD.bits_from_unfold (G.reveal gsrc) (U32.v g + 2);
      SD.bits_from_unfold (G.reveal gsrc) (U32.v g + 3);
      append4 (SD.bit_at (G.reveal gsrc) (U32.v g)) (SD.bit_at (G.reveal gsrc) (U32.v g + 1))
              (SD.bit_at (G.reveal gsrc) (U32.v g + 2)) (SD.bit_at (G.reveal gsrc) (U32.v g + 3))
              (SD.bits_from (G.reveal gsrc) (U32.v g + 4));
      assert (SD.bits_from (G.reveal gsrc) (U32.v g) ==
              SDfa.nibble_bits (U32.v nib) `L.append` SD.bits_from (G.reveal gsrc) (U32.v g + 4));
      (* one nibble step == stepping decode_go by those four bits *)
      SDfa.step_unfold (RDT.state_of (U32.v cur)) (U32.v nib);
      RDfa.decode_go_nibble (SDfa.nibble_bits (U32.v nib))
                            (SD.bits_from (G.reveal gsrc) (U32.v g + 4))
                            (G.reveal gacc) (G.reveal gnbits) (G.reveal gout);
      let c = read_cell cur nib in
      let next = U32.div c 65536ul in
      (* cell_ok_post c: state_of next == fst(step (state_of cur) nib), emit == snd *)
      if U32.eq next 256ul then begin
        (* next-state is the fail state: state_of 256 == DFail, so the spec is None *)
        B.upd out_len 0ul written;
        (-1l)
      end else begin
        let gacc'   : G.erased nat = G.hide (SDfa.DLive?.acc (RDT.state_of (U32.v next))) in
        let gnbits' : G.erased nat = G.hide (SDfa.DLive?.nbits (RDT.state_of (U32.v next))) in
        let flag = U32.rem (U32.div c 256ul) 256ul in
        if U32.eq flag 1ul then begin
          (* the nibble emits one byte (sym); spec advances `gout @ [sym]` *)
          let sym = U32.rem c 256ul in
          if U32.lt written dst_cap then begin
            B.upd dst written (Cast.uint32_to_uint8 sym);
            let h1 = get () in
            RD.decoded_prefix_upd_snoc (B.as_seq h0 dst) (U32.v written) (Cast.uint32_to_uint8 sym);
            let gout' : G.erased (list SC.byte) =
              G.elift1 (fun (l:list SC.byte) -> l @ [U32.v sym]) gout in
            assert (G.reveal gout' == RD.decoded_prefix (B.as_seq h1 dst) (U32.v written + 1));
            assert (B.as_seq h1 src == G.reveal gsrc);
            dfa_loop src dst src_len dst_cap (U32.add g 4ul) next (U32.add written 1ul)
                     gsrc gout' gacc' gnbits' out_len
          end else begin
            (* dst full but spec keeps emitting: spec length > dst_cap, obligation vacuous *)
            RD.decode_go_grows (SD.bits_from (G.reveal gsrc) (U32.v g + 4))
                               (G.reveal gacc') (G.reveal gnbits') (G.reveal gout @ [U32.v sym]);
            RD.len_snoc (G.reveal gout) (U32.v sym);
            B.upd out_len 0ul written;
            (-1l)
          end
        end else
          (* no emit: spec advances to the next state with the same output *)
          dfa_loop src dst src_len dst_cap (U32.add g 4ul) next written
                   gsrc gout gacc' gnbits' out_len
      end
    end
#pop-options

(* ---------------------------------------------------------------------- *)
(* Public entry: decode via the nibble DFA from the start state            *)
(* ---------------------------------------------------------------------- *)

#push-options "--fuel 2 --ifuel 1 --z3rlimit 80"
let decode_dfa src src_len dst dst_cap out_len =
  assert_norm (RDT.state_of 0 == SDfa.DLive 0 0);
  let h = get () in
  let gsrc0 : G.erased (Seq.seq U8.t) = G.hide (B.as_seq h src) in
  let gout0 : G.erased (list SC.byte) = G.hide [] in
  (* the loop's spec at (g=0, acc=0, nbits=0, out=[]) is exactly decode_bits of the
     byte buffer's bit view (both `decode_bits`/`bytes_to_bits` are definitional) *)
  assert (SD.bytes_to_bits (B.as_seq h src) == SD.bits_from (G.reveal gsrc0) 0);
  assert (G.reveal gout0 == []);
  assert (SC.decode_bits (SD.bytes_to_bits (B.as_seq h src))
          == SC.decode_go (SD.bits_from (G.reveal gsrc0) 0) 0 0 (G.reveal gout0));
  dfa_loop src dst src_len dst_cap 0ul 0ul 0ul gsrc0 gout0 (G.hide 0) (G.hide 0) out_len
#pop-options
