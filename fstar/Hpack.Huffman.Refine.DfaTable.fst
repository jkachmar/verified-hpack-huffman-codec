module Hpack.Huffman.Refine.DfaTable

/// A normalizer-fast restatement of the DFA model, used to build and verify the
/// executable transition table (D3) by reduction rather than SMT.
///
/// The spec's `lookup_v` (via `find_v`) re-walks the 257-entry table with
/// `L.index` on every iteration — O(n²) per lookup — so normalising `step` across
/// the ~4 K table cells is intractable (measured ~2 s/cell). `lookup_fast` makes a
/// single O(n) pass over the table list; `step_fast` is `Spec.Dfa.step` built on
/// it. Each is proved equal to its spec counterpart once and for all here, so the
/// table builder can normalise `step_fast` (sub-millisecond/cell) while every
/// downstream proof keeps talking about the spec `step` / `decode_go`.

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
module IB = LowStar.ImmutableBuffer

#set-options "--fuel 1 --ifuel 1 --z3rlimit 40"

(* ---------------------------------------------------------------------- *)
(* Single-pass codeword lookup                                             *)
(* ---------------------------------------------------------------------- *)

/// Scan a table suffix for the symbol whose code is the `k`-bit value `v`. The
/// index refinement (`i + length l == 257`) keeps the returned index a `sym`.
let rec find_l (l:list entry) (i:nat{i + L.length l == 257}) (v k:nat)
  : Tot (option sym) (decreases l) =
  match l with
  | [] -> None
  | e :: tl -> if e.len = k && e.code = v then Some i
               else find_l tl (i + 1) v k

let lookup_fast (v k:nat) : option sym =
  assert_norm (L.length hpack_table == 257);
  find_l hpack_table 0 v k

/// `find_l` over the `i`-suffix of the table agrees with `find_v` from `i`.
let rec find_l_eq (l:list entry) (i:nat{i + L.length l == 257}) (v k:nat)
  : Lemma
      (requires (forall (j:nat). j < L.length l ==> L.index l j == entry_at (i + j)))
      (ensures find_l l i v k == find_v v k i)
      (decreases l)
  = match l with
    | [] -> ()
    | e :: tl ->
        assert (e == entry_at i);                       // forall at j = 0
        introduce forall (j:nat). j < L.length tl ==> L.index tl j == entry_at ((i + 1) + j)
        with introduce _ ==> _
          with _. assert (L.index tl j == L.index (e :: tl) (j + 1));
        find_l_eq tl (i + 1) v k

let lookup_fast_correct (v k:nat)
  : Lemma (lookup_fast v k == lookup_v v k)
  = assert_norm (L.length hpack_table == 257);
    find_l_eq hpack_table 0 v k

(* ---------------------------------------------------------------------- *)
(* The DFA step, on the fast lookup                                        *)
(* ---------------------------------------------------------------------- *)

let bit_step_fast (s:dstate) (b:bool) : dstate & option byte =
  match s with
  | DFail -> DFail, None
  | DLive acc nbits ->
      let acc' = acc * 2 + (if b then 1 else 0) in
      let nbits' = nbits + 1 in
      (match lookup_fast acc' nbits' with
       | Some sy -> if sy = eos_index then DFail, None else DLive 0 0, Some sy
       | None -> DLive acc' nbits', None)

let bit_step_fast_eq (s:dstate) (b:bool)
  : Lemma (bit_step_fast s b == bit_step s b)
  = match s with
    | DFail -> ()
    | DLive acc nbits -> lookup_fast_correct (acc * 2 + (if b then 1 else 0)) (nbits + 1)

let rec bits_step_fast (s:dstate) (bs:list bool)
  : Tot (dstate & list byte) (decreases bs) =
  match bs with
  | [] -> s, []
  | b :: tl ->
      let s1, o1 = bit_step_fast s b in
      let s2, o2 = bits_step_fast s1 tl in
      s2, (match o1 with None -> [] | Some ob -> [ob]) @ o2

let rec bits_step_fast_eq (s:dstate) (bs:list bool)
  : Lemma (ensures bits_step_fast s bs == bits_step s bs) (decreases bs)
  = match bs with
    | [] -> ()
    | b :: tl ->
        bit_step_fast_eq s b;
        bits_step_fast_eq (fst (bit_step s b)) tl

let step_fast (s:dstate) (n:nibble) : dstate & list byte =
  bits_step_fast s (nibble_bits n)

let step_fast_eq (s:dstate) (n:nibble)
  : Lemma (step_fast s n == step s n)
  = bits_step_fast_eq s (nibble_bits n)

(* `state_of`, `cell_next`, `cell_emit`, and the `dfa_chunk_list` selector are the
   transparent accessors exposed in the interface (Hpack.Huffman.Refine.DfaTable.fsti)
   — definitions there, visible here. *)

(* ---------------------------------------------------------------------- *)
(* Chunk access: the selector and the buffer-of-buffers recall helper.      *)
(* Hand-written here (not generator-emitted) so the generator only ever      *)
(* produces data; all proof reasoning is human-authored and reviewed.        *)
(* ---------------------------------------------------------------------- *)

(* `dfa_chunk_list` (the 16-way selector) is exposed transparently in the interface. *)

(* The buffer-of-buffers recall helper (`outer_chunk`) is gone: reading a chunk
   for a dynamic id is done by `Hpack.Huffman.Lowstar.Dfa.read_cell`, a 16-way
   `match` over the concrete chunk buffers (a C `switch`), so each branch recalls a
   named buffer directly — no per-element witness over a buffer-of-buffers. *)

(* ---------------------------------------------------------------------- *)
(* The emitted table (chunked) matches the spec step, cell by cell          *)
(* ---------------------------------------------------------------------- *)

/// Cell at chunk `k`, offset `off` (flat position `p = chunk_size*k + off`) is
/// correct: valid next-id, names the spec step's next state, emits its output.
let chunk_cell_ok (k:nat{k < dfa_n_chunks}) (off:nat{off < dfa_chunk_size}) (c:U32.t) : bool =
  let p = dfa_chunk_size * k + off in
  let nn : nibble = p % 16 in
  let r = step_fast (state_of (p / 16)) nn in
  (cell_next c <= dfa_n_states) && (state_of (cell_next c) = fst r) && (cell_emit c = snd r)

/// Single pass over one chunk, threading the offset (the `find_l` idiom).
let rec check_chunk (k:nat{k < dfa_n_chunks}) (off:nat)
  (tbl:list U32.t{off + L.length tbl == dfa_chunk_size})
  : Tot bool (decreases tbl) =
  match tbl with
  | [] -> true
  | c :: rest -> chunk_cell_ok k off c && check_chunk k (off + 1) rest

/// Single pass over all chunks.
let rec check_all (k:nat) : Tot bool (decreases (dfa_n_chunks - k)) =
  if k >= dfa_n_chunks then true
  else check_chunk k 0 (dfa_chunk_list k) && check_all (k + 1)

/// The bulk normalisation: every cell of every chunk is correct.
let check_all_holds (_:unit) : Lemma (check_all 0) = assert_norm (check_all 0)

/// Per-offset extraction within a chunk (`find_l_eq` idiom).
let rec check_chunk_index (k:nat{k < dfa_n_chunks}) (off:nat)
  (tbl:list U32.t{off + L.length tbl == dfa_chunk_size}) (j:nat)
  : Lemma (requires check_chunk k off tbl /\ j < L.length tbl)
          (ensures chunk_cell_ok k (off + j) (L.index tbl j)) (decreases tbl)
  = match tbl with
    | c :: rest ->
        assert (check_chunk k off (c :: rest) ==
                (chunk_cell_ok k off c && check_chunk k (off + 1) rest));
        if j = 0 then () else check_chunk_index k (off + 1) rest (j - 1)

/// Per-chunk extraction across chunks (the `cover_all_index` idiom).
let rec check_all_index (k0 k:nat)
  : Lemma (requires check_all k0 /\ k0 <= k /\ k < dfa_n_chunks)
          (ensures check_chunk k 0 (dfa_chunk_list k)) (decreases (dfa_n_chunks - k0))
  = if k0 = k then ()
    else (assert (check_all k0 == (check_chunk k0 0 (dfa_chunk_list k0) && check_all (k0 + 1)));
          check_all_index (k0 + 1) k)

/// Chunk `k`, offset `off` of the table agrees with the spec `step`: in terms of
/// the flat position `p = chunk_size*k + off`, its next-id names step's next state
/// and its emit is step's output. (D4 reads `dfa_chunks[k][off]` and applies this.)
let chunk_table_ok (k:nat{k < dfa_n_chunks}) (off:nat{off < dfa_chunk_size})
  : Lemma (let c = L.index (dfa_chunk_list k) off in
           let p = dfa_chunk_size * k + off in
           cell_next c <= dfa_n_states /\
           state_of (cell_next c) == fst (step (state_of (p / 16)) (p % 16)) /\
           cell_emit c == snd (step (state_of (p / 16)) (p % 16)))
  = check_all_holds ();
    check_all_index 0 k;
    check_chunk_index k 0 (dfa_chunk_list k) off;
    let p = dfa_chunk_size * k + off in
    step_fast_eq (state_of (p / 16)) (p % 16)

(* ---------------------------------------------------------------------- *)
(* The per-state accept flag matches spec acceptance                       *)
(* ---------------------------------------------------------------------- *)

let accept_ok_at (i:nat{i < dfa_n_states}) (av:U8.t) : bool =
  U8.v av = (if is_accepting (state_of i) then 1 else 0)

let rec check_acc (i:nat) (l:list U8.t{i + L.length l == dfa_n_states})
  : Tot bool (decreases l) =
  match l with
  | [] -> true
  | av :: rest -> accept_ok_at i av && check_acc (i + 1) rest

let check_acc_holds (_:unit) : Lemma (check_acc 0 dfa_accept_list) =
  assert_norm (check_acc 0 dfa_accept_list)

let rec check_acc_index (i:nat) (l:list U8.t{i + L.length l == dfa_n_states}) (j:nat)
  : Lemma (requires check_acc i l /\ j < L.length l)
          (ensures accept_ok_at (i + j) (L.index l j)) (decreases l)
  = match l with
    | av :: rest ->
        assert (check_acc i (av :: rest) == (accept_ok_at i av && check_acc (i + 1) rest));
        if j = 0 then () else check_acc_index (i + 1) rest (j - 1)

let table_accept_ok (i:nat{i < dfa_n_states})
  : Lemma (U8.v (Seq.index dfa_accept_contents i)
           = (if is_accepting (state_of i) then 1 else 0))
  = check_acc_holds ();
    assert_norm (L.length dfa_accept_list == dfa_n_states);
    check_acc_index 0 dfa_accept_list i;
    reveal_opaque (`%dfa_accept_contents) dfa_accept_contents;
    Seq.lemma_seq_of_list_index dfa_accept_list i
