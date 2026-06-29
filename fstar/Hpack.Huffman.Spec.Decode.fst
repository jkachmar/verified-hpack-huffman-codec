module Hpack.Huffman.Spec.Decode

/// The decoder's view of a byte buffer as an MSB-first bit string, and the
/// decode facts stated over bytes (rather than over an abstract `list bool`).
///
///   * `bit_at` / `bits_from` / `bytes_to_bits` — the bits of a byte sequence,
///     most-significant bit first within each byte. `bit_at s g` is exactly the
///     bit `Hpack.Huffman.Lowstar.Codec.decode_loop` reads at global index `g`
///     (`(src[g/8] >> (7 - g%8)) & 1`), and `bits_from s g` is the suffix the
///     loop has left to process at step `g`. This is the bridge the imperative
///     simulation (`Hpack.Huffman.Bridge.Decode`) will be stated over.
///
/// Purely the byte<->bit mapping; no codec reasoning lives here yet.

open FStar.Mul
module L = FStar.List.Tot
module Seq = FStar.Seq
module U8 = FStar.UInt8
module M = FStar.Math.Lemmas

#set-options "--fuel 1 --ifuel 1 --z3rlimit 40"

/// `g/8 < length` whenever `g < 8*length` (division by the literal 8).
let byte_index_bound (s:Seq.seq U8.t) (g:nat{g < 8 * Seq.length s})
  : Lemma (g / 8 < Seq.length s)
  = M.lemma_div_lt_nat g (8 * Seq.length s) 8 |> (fun () -> ());
    M.lemma_div_le g (8 * Seq.length s - 1) 8

/// The `g`-th bit of `s`, MSB-first within each byte — exactly the bit
/// `decode_loop` reads at global index `g`.
let bit_at (s:Seq.seq U8.t) (g:nat{g < 8 * Seq.length s}) : bool =
  byte_index_bound s g;
  (U8.v (Seq.index s (g / 8)) / pow2 (7 - g % 8)) % 2 = 1

/// `bit_at`'s value, with the bounds proof discharged — lets the Low* decoder
/// (which computes the same `(byte >> shift) & 1`) line its read up with the spec
/// bit without unfolding `bit_at` through its internal lemma call.
let bit_at_val (s:Seq.seq U8.t) (g:nat{g < 8 * Seq.length s})
  : Lemma (byte_index_bound s g;
           bit_at s g == ((U8.v (Seq.index s (g / 8)) / pow2 (7 - g % 8)) % 2 = 1))
  = ()

/// The bits of `s` from global index `g` onward (MSB-first): what `decode_loop`
/// still has to process at step `g`.
let rec bits_from (s:Seq.seq U8.t) (g:nat{g <= 8 * Seq.length s})
  : Tot (list bool) (decreases (8 * Seq.length s - g))
  = if g = 8 * Seq.length s then []
    else bit_at s g :: bits_from s (g + 1)

/// The full MSB-first bit string of `s`.
let bytes_to_bits (s:Seq.seq U8.t) : list bool = bits_from s 0

/// `bits_from s g` has exactly `8*length - g` bits.
let rec bits_from_length (s:Seq.seq U8.t) (g:nat{g <= 8 * Seq.length s})
  : Lemma (ensures L.length (bits_from s g) == 8 * Seq.length s - g)
          (decreases (8 * Seq.length s - g))
  = if g = 8 * Seq.length s then () else bits_from_length s (g + 1)

/// One-step unfold of `bits_from` (definitional; stated for the simulation).
let bits_from_unfold (s:Seq.seq U8.t) (g:nat{g < 8 * Seq.length s})
  : Lemma (bits_from s g == bit_at s g :: bits_from s (g + 1)) = ()

/// At the end of input `bits_from` is empty (definitional; lets the decoder's
/// base case avoid unfolding `bits_from` when run at `--fuel 0`).
let bits_from_nil (s:Seq.seq U8.t) (g:nat{g <= 8 * Seq.length s})
  : Lemma (requires g == 8 * Seq.length s) (ensures bits_from s g == []) = ()
