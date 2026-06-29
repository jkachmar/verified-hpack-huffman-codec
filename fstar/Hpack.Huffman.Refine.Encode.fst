module Hpack.Huffman.Refine.Encode

/// The executable per-byte encode tables (`Hpack.Huffman.Lowstar.Tables.huff_code`
/// / `huff_len`) hold exactly the spec's code and length for every byte:
///
///   * `huff_code_correct b` : `huff_code_contents[b] == code_of b`
///   * `huff_len_correct  b` : `huff_len_contents[b]  == len_of  b`
///
/// Proved over the named list forms by normalisation (`enc_wf` walks the encode
/// lists against the spec `hpack_table`) and transported onto the `_contents`
/// sequences via the opaque-reveal + `lemma_seq_of_list_index` idiom. So the
/// encoder's table *values* are under proof, not assumed.

open Hpack.Huffman.Table
open Hpack.Huffman.Spec.Codec
open Hpack.Huffman.Lowstar.Tables
module L = FStar.List.Tot
module S = FStar.Seq
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module P = Hpack.Huffman.Table.Properties
module Lst = Hpack.Huffman.Util.List
module BS = Hpack.Huffman.Util.Bits

#set-options "--fuel 2 --ifuel 2 --z3rlimit 40"

(* ---------------------------------------------------------------------- *)
(* seq <-> list bridges (opaque-reveal + lemma_seq_of_list_index idiom)    *)
(* ---------------------------------------------------------------------- *)

let list_lens () : Lemma (L.length huff_code_list == 256 /\ L.length huff_len_list == 256) =
  assert_norm (L.length huff_code_list == 256);
  assert_norm (L.length huff_len_list == 256)

let code_idx (i:nat) : Lemma
  (requires i < 256 /\ L.length huff_code_list == 256)
  (ensures S.index huff_code_contents i == L.index huff_code_list i) =
  reveal_opaque (`%huff_code_contents) huff_code_contents

let len_idx (i:nat) : Lemma
  (requires i < 256 /\ L.length huff_len_list == 256)
  (ensures S.index huff_len_contents i == L.index huff_len_list i) =
  reveal_opaque (`%huff_len_contents) huff_len_contents

(* ---------------------------------------------------------------------- *)
(* Encode lists match the spec table, entry by entry                       *)
(* ---------------------------------------------------------------------- *)

/// `cs[i] = es[i].code` and `ls[i] = es[i].len` for the whole encode prefix
/// (the encode lists are the first 256 entries of the 257-entry spec table).
let rec enc_wf (cs:list U32.t) (ls:list (x:U8.t{5 <= U8.v x /\ U8.v x <= 30}))
               (es:list entry) : Tot bool (decreases cs) =
  match cs, ls, es with
  | c :: ct, l :: lt, e :: et -> (U32.v c = e.code && U8.v l = e.len) && enc_wf ct lt et
  | [], [], _ -> true
  | _ -> false

let rec enc_wf_index (cs:list U32.t) (ls:list (x:U8.t{5 <= U8.v x /\ U8.v x <= 30}))
                     (es:list entry) (i:nat)
  : Lemma (requires enc_wf cs ls es /\ L.length ls == L.length cs /\
                    i < L.length cs /\ L.length cs <= L.length es)
          (ensures U32.v (L.index cs i) == (L.index es i).code /\
                   U8.v (L.index ls i) == (L.index es i).len)
          (decreases cs)
  = match cs, ls, es with
    | c :: ct, l :: lt, e :: et -> if i = 0 then () else enc_wf_index ct lt et (i - 1)

let huff_tables_wf () : Lemma (enc_wf huff_code_list huff_len_list hpack_table) =
  assert_norm (enc_wf huff_code_list huff_len_list hpack_table)

(* ---------------------------------------------------------------------- *)
(* The committed contents equal the spec code / length per byte            *)
(* ---------------------------------------------------------------------- *)

let huff_code_correct (b:byte)
  : Lemma (U32.v (S.index huff_code_contents b) == code_of b)
  = P.lemma_table_complete (); list_lens (); huff_tables_wf ();
    enc_wf_index huff_code_list huff_len_list hpack_table b;   // L.index huff_code_list b == (hpack_table[b]).code
    code_idx b                                                 // contents[b] == huff_code_list[b]
    // code_of b == (entry_at b).code == (hpack_table[b]).code

let huff_len_correct (b:byte)
  : Lemma (U8.v (S.index huff_len_contents b) == len_of b)
  = P.lemma_table_complete (); list_lens (); huff_tables_wf ();
    enc_wf_index huff_code_list huff_len_list hpack_table b;
    len_idx b

(* ---------------------------------------------------------------------- *)
(* The emitted byte stream, as bits                                        *)
(*                                                                         *)
(* `enc_bits s n` is the MSB-first bit string of the first `n` bytes of    *)
(* `s` (8 bits/byte) — the encoder's `dst` prefix, mirroring `decoded_     *)
(* prefix` on the decode side. The update lemmas describe writing a byte   *)
(* at the cursor; `encode_bits_snoc` lets the per-symbol step grow the     *)
(* spec output by one code.                                                *)
(* ---------------------------------------------------------------------- *)

(* `enc_bits` is the transparent definition exposed in the interface. *)

/// Updating `s` at index `i >= n` leaves its first-`n` bit prefix unchanged.
let rec enc_bits_upd (s:Seq.seq U8.t) (i:nat) (v:U8.t) (n:nat{n <= i /\ i < Seq.length s})
  : Lemma (ensures enc_bits (Seq.upd s i v) n == enc_bits s n) (decreases n)
  = if n = 0 then ()
    else (enc_bits_upd s i v (n - 1); Seq.lemma_index_upd2 s i v (n - 1))

/// Writing `v` at the cursor `n` appends `v`'s 8 bits to the first-`n` prefix.
let enc_bits_upd_snoc (s:Seq.seq U8.t) (n:nat{n < Seq.length s}) (v:U8.t)
  : Lemma (enc_bits (Seq.upd s n v) (n + 1) == enc_bits s n @ BS.code_to_bits (U8.v v) 8)
  = enc_bits_upd s n v n; Seq.lemma_index_upd1 s n v

/// Each code fits its own bit-length (RFC invariant), so the encoder's shift-or
/// append has no overlap. (`Table.Properties.fits` per byte.)
let code_fits (b:byte) : Lemma (code_of b < pow2 (len_of b))
  = P.lemma_table_complete (); P.lemma_all_fit ();
    Lst.all_pred_index P.fits hpack_table b

/// `enc_bits` reads only the first `n` bytes, so a wider `m`-byte prefix (e.g. a
/// `gsub`/slice of the encoded buffer) carries the same first-`n` bits.
let rec enc_bits_prefix (s:Seq.seq U8.t) (n m:nat)
  : Lemma (requires n <= m /\ m <= Seq.length s)
          (ensures enc_bits s n == enc_bits (Seq.slice s 0 m) n) (decreases n)
  = if n = 0 then ()
    else (enc_bits_prefix s (n - 1) m;
          Seq.lemma_index_slice s 0 m (n - 1))   // (slice s 0 m).[n-1] == s.[n-1]

/// `encode_bits` grows by one code when a byte is appended to the input.
let rec encode_bits_snoc (l:list byte) (b:byte)
  : Lemma (ensures encode_bits (l @ [b]) == encode_bits l @ code_bits_of b) (decreases l)
  = match l with
    | [] -> ()
    | x :: tl -> encode_bits_snoc tl b; L.append_assoc (code_bits_of x) (encode_bits tl) (code_bits_of b)
