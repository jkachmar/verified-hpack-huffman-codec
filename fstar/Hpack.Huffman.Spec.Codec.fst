module Hpack.Huffman.Spec.Codec

/// The RFC 7541 §5.2 Huffman codec as pure mathematics over the code table.
/// Symbols are naturals (`byte` 0..255, plus the EOS index 256); bit
/// strings are `list bool`, MSB first.
///
///   * `code_bits_of` / `encode_bits` — a symbol's code bits, and the
///     concatenated (unpadded) encoding of a byte string;
///   * `find_v` / `lookup_v` — locate the symbol whose code is a given
///     (length, value) pair, by linear scan over the table;
///   * `decode_go` / `decode_bits` — the greedy MSB-first decoder: read bits into
///     an accumulator, emit on a codeword match, reject an in-stream EOS, and
///     require leftover bits at end-of-input to be valid padding (≤ 7 bits, all
///     ones — a strict prefix of the all-ones EOS code).

open Hpack.Huffman.Table
open FStar.Mul
open FStar.List.Tot
module L = FStar.List.Tot
module BS = Hpack.Huffman.Util.Bits

/// A symbol index: bytes are 0..255, 256 is EOS.
noextract let sym = s:nat{s < 257}
noextract let byte = s:nat{s < 256}
noextract let eos_index : nat = 256

noextract let entry_at (s:sym) : entry =
  (let _ = assert_norm (L.length hpack_table == 257) in L.index hpack_table s)

noextract let code_of (s:sym) : nat = (entry_at s).code
noextract let len_of  (s:sym) : nat = (entry_at s).len

/// The bit string of a symbol's code.
noextract let code_bits_of (s:sym) : list bool =
  let e = entry_at s in BS.code_to_bits e.code e.len

(* ---------------------------------------------------------------------- *)
(* Codeword lookup                                                        *)
(* ---------------------------------------------------------------------- *)

/// Find the symbol whose code is the `k`-bit value `v` (length and value both
/// match). Returns the first such symbol; distinctness (proved in the lookup
/// layer) makes it the only one. Works in the division representation, so it
/// connects directly to the table's (division-based) prefix-freeness.
noextract let rec find_v (v:nat) (k:nat) (i:nat{i <= 257})
  : Tot (option sym) (decreases (257 - i)) =
  if i = 257 then None
  else (let e = entry_at i in
        if e.len = k && e.code = v then Some i else find_v v k (i + 1))

noextract let lookup_v (v:nat) (k:nat) : option sym = find_v v k 0

(* ---------------------------------------------------------------------- *)
(* Decoding and encoding                                                  *)
(* ---------------------------------------------------------------------- *)

/// Valid trailing padding: at most 7 bits, and the `nbits`-bit value is all
/// ones (= 2^nbits - 1), i.e. a strict prefix of the all-ones EOS code.
noextract let valid_padding_v (acc nbits:nat) : bool =
  nbits <= 7 && acc = pow2 nbits - 1

/// Greedy decoder over a (value, nbits) accumulator: read bits MSB-first, emit
/// on a codeword match (and reset), treat EOS-in-stream as an error, and require
/// leftover bits at EOF to be valid padding.
noextract let rec decode_go (input:list bool) (acc nbits:nat) (out:list byte)
  : Tot (option (list byte)) (decreases (L.length input)) =
  match input with
  | [] -> if valid_padding_v acc nbits then Some out else None
  | b :: rest ->
      let acc' = acc * 2 + (if b then 1 else 0) in
      let nbits' = nbits + 1 in
      (match lookup_v acc' nbits' with
       | Some s -> if s = eos_index then None else decode_go rest 0 0 (out @ [s])
       | None -> decode_go rest acc' nbits' out)

noextract let decode_bits (input:list bool) : option (list byte) =
  decode_go input 0 0 []

/// Encode a list of bytes to the concatenated code bit stream (no padding).
noextract let rec encode_bits (bs:list byte) : list bool =
  match bs with
  | [] -> []
  | b :: tl -> code_bits_of b @ encode_bits tl
