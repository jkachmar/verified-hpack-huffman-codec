module Hpack.Huffman.Refine.Encode

/// Interface: the executable per-byte encode tables equal the spec, and the
/// encoder's emitted bit stream as a `dst` prefix.
///
/// Exposed: `huff_code_correct`/`huff_len_correct` (each byte's committed code/len
/// equals the spec's `code_of`/`len_of`), the transparent `enc_bits` (a `dst`
/// prefix read MSB-first) and the lemmas the Low\* encoder + round-trip need over
/// it (`enc_bits_upd_snoc`, `enc_bits_prefix`, `code_fits`, `encode_bits_snoc`).
/// Sealed in the `.fst`: the normalisation machinery (`enc_wf`/`enc_wf_index`/
/// `huff_tables_wf`), the opaque-reveal bridges (`list_lens`/`code_idx`/`len_idx`),
/// and the `enc_bits_upd` helper.

open Hpack.Huffman.Spec.Codec
open Hpack.Huffman.Lowstar.Tables
open FStar.Mul
module L = FStar.List.Tot
module S = FStar.Seq
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module BS = Hpack.Huffman.Util.Bits

/// The committed encode tables hold exactly the spec's code / length per byte.
val huff_code_correct (b:byte)
  : Lemma (U32.v (S.index huff_code_contents b) == code_of b)
val huff_len_correct (b:byte)
  : Lemma (U8.v (S.index huff_len_contents b) == len_of b)

/// `enc_bits s n` is the MSB-first bit string of the first `n` bytes of `s`
/// (8 bits/byte) — the encoder's `dst` prefix, mirroring `decoded_prefix` on the
/// decode side.
let rec enc_bits (s:S.seq U8.t) (n:nat{n <= S.length s}) : Tot (list bool) (decreases n) =
  if n = 0 then [] else enc_bits s (n - 1) @ BS.code_to_bits (U8.v (S.index s (n - 1))) 8

/// Writing `v` at the cursor `n` appends `v`'s 8 bits to the first-`n` prefix.
val enc_bits_upd_snoc (s:S.seq U8.t) (n:nat{n < S.length s}) (v:U8.t)
  : Lemma (enc_bits (S.upd s n v) (n + 1) == enc_bits s n @ BS.code_to_bits (U8.v v) 8)

/// Each code fits its own bit-length (RFC invariant), so the shift-or append has
/// no overlap.
val code_fits (b:byte) : Lemma (code_of b < pow2 (len_of b))

/// `enc_bits` reads only the first `n` bytes, so a wider `m`-byte prefix (e.g. a
/// slice of the encoded buffer) carries the same first-`n` bits.
val enc_bits_prefix (s:S.seq U8.t) (n m:nat)
  : Lemma (requires n <= m /\ m <= S.length s)
          (ensures enc_bits s n == enc_bits (S.slice s 0 m) n)

/// `encode_bits` grows by one code when a byte is appended to the input.
val encode_bits_snoc (l:list byte) (b:byte)
  : Lemma (encode_bits (l @ [b]) == encode_bits l @ code_bits_of b)
