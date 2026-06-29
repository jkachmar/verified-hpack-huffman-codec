module Hpack.Huffman.Lowstar.RoundTrip

/// The end-to-end capstone: composing the verified `encode` and `decode` recovers
/// the input. This bridges the encoder's byte-granular output view
/// (`Refine.Encode.enc_bits`) to the decoder's bit-granular input view
/// (`Spec.Decode.bytes_to_bits`), then feeds `encode`'s output through `decode`
/// and discharges `decode`'s acceptance hypothesis via `Spec.RoundTrip`.

open FStar.HyperStack.ST
open FStar.Mul
module L   = FStar.List.Tot
module Seq = FStar.Seq
module B   = LowStar.Buffer
module MB  = LowStar.Monotonic.Buffer
module U8  = FStar.UInt8
module U32 = FStar.UInt32
module I32 = FStar.Int32
module M   = FStar.Math.Lemmas
module BS  = Hpack.Huffman.Util.Bits
module SC  = Hpack.Huffman.Spec.Codec
module SD  = Hpack.Huffman.Spec.Decode
module SR  = Hpack.Huffman.Spec.RoundTrip
module RE  = Hpack.Huffman.Refine.Encode
module RD  = Hpack.Huffman.Bridge.Decode
module LC  = Hpack.Huffman.Lowstar.Codec
module LD  = Hpack.Huffman.Lowstar.Dfa
open Hpack.Huffman.Lowstar.Tables

#set-options "--fuel 1 --ifuel 1 --z3rlimit 40"

(* ---------------------------------------------------------------------- *)
(* bytes_to_bits (bit-granular) == enc_bits (byte-granular)                *)
(* ---------------------------------------------------------------------- *)

/// Peel the low `r` bits of byte `j` off the front of `bits_from`: the suffix of
/// byte `j`'s MSB-first bits, `code_to_bits (s[j] % 2^r) r`, sits ahead of the
/// rest of the stream. At `r = 8` this peels a whole byte. Induction on `r`.
#push-options "--fuel 2 --ifuel 1 --z3rlimit 60"
let rec byte_peel (s:Seq.seq U8.t) (j:nat{j < Seq.length s}) (r:nat{r <= 8})
  : Lemma (ensures SD.bits_from s (8 * j + (8 - r))
                   == BS.code_to_bits (U8.v (Seq.index s j) % pow2 r) r
                      @ SD.bits_from s (8 * (j + 1)))
          (decreases r)
  = if r = 0 then ()                                 // index == 8(j+1); code_to_bits _ 0 == []
    else begin
      let g = 8 * j + (8 - r) in
      assert_norm (pow2 1 == 2);
      SD.bits_from_unfold s g;                        // bits_from g == bit_at g :: bits_from (g+1)
      SD.bit_at_val s g;                              // bit_at g == (s[g/8] / 2^(7 - g%8)) % 2 == 1
      M.lemma_div_mod g 8;                            // g/8 == j, g%8 == 8-r  (0 <= 8-r < 8)
      M.pow2_modulo_division_lemma_1 (U8.v (Seq.index s j)) (r - 1) r;   // (a%2^r)/2^(r-1) == (a/2^(r-1))%2
      M.pow2_modulo_modulo_lemma_1 (U8.v (Seq.index s j)) (r - 1) r;     // (a%2^r)%2^(r-1) == a%2^(r-1)
      BS.code_to_bits_unfold (U8.v (Seq.index s j) % pow2 r) r;
      byte_peel s j (r - 1)
    end
#pop-options

/// `enc_bits s n` (the first `n` bytes' bits) followed by the rest of the stream
/// from bit `8n` is the whole stream — by peeling one byte per step.
#push-options "--fuel 2 --ifuel 1 --z3rlimit 60"
let rec bits_from_enc_aux (s:Seq.seq U8.t) (n:nat{n <= Seq.length s})
  : Lemma (ensures RE.enc_bits s n @ SD.bits_from s (8 * n) == SD.bits_from s 0)
          (decreases n)
  = if n = 0 then ()                                  // enc_bits s 0 == [] ; [] @ x == x
    else begin
      assert_norm (pow2 8 == 256);                    // U8.v s[n-1] % 2^8 == U8.v s[n-1]
      M.small_mod (U8.v (Seq.index s (n - 1))) (pow2 8);
      byte_peel s (n - 1) 8;                          // bits_from (8(n-1)) == code_to_bits s[n-1] 8 @ bits_from (8n)
      L.append_assoc (RE.enc_bits s (n - 1))
                     (BS.code_to_bits (U8.v (Seq.index s (n - 1))) 8)
                     (SD.bits_from s (8 * n));
      bits_from_enc_aux s (n - 1)
    end
#pop-options

/// THE VIEW BRIDGE: the decoder's `bytes_to_bits` of `s` equals the encoder's
/// `enc_bits` of all of `s` — the same bit string, built byte- vs bit-granularly.
let bytes_to_bits_enc_bits (s:Seq.seq U8.t)
  : Lemma (SD.bytes_to_bits s == RE.enc_bits s (Seq.length s))
  = bits_from_enc_aux s (Seq.length s);
    SD.bits_from_nil s (8 * Seq.length s);            // bits_from s (8*length) == []
    L.append_l_nil (RE.enc_bits s (Seq.length s))     // enc_bits @ [] == enc_bits

(* ---------------------------------------------------------------------- *)
(* THE CAPSTONE: decode (encode x) == x on the real extracted C            *)
(* ---------------------------------------------------------------------- *)

/// Pure glue: if `enc`'s first `r` bytes are `encode_bits xs` ∥ ≤7 all-ones
/// padding (exactly `encode`'s `ensures`), then decoding those bytes' bit stream
/// yields `xs`. The `decode_bits` hypothesis `decode` needs, distilled — and
/// kept out of the `Stack` body so the existential elimination stays pure.
let round_trip_bridge (encs:Seq.seq U8.t) (r:nat{r <= Seq.length encs}) (xs:list SC.byte)
  : Lemma (requires (exists (k:nat). k <= 7 /\
                       RE.enc_bits encs r == SC.encode_bits xs @ BS.code_to_bits (pow2 k - 1) k))
          (ensures SC.decode_bits (SD.bytes_to_bits (Seq.slice encs 0 r)) == Some xs)
  = RE.enc_bits_prefix encs r r;                      // enc_bits (slice encs 0 r) r == enc_bits encs r
    bytes_to_bits_enc_bits (Seq.slice encs 0 r);      // bytes_to_bits (slice) == enc_bits (slice) r
    eliminate exists (k:nat). (k <= 7 /\
                 RE.enc_bits encs r == SC.encode_bits xs @ BS.code_to_bits (pow2 k - 1) k)
    returns (SC.decode_bits (SD.bytes_to_bits (Seq.slice encs 0 r)) == Some xs)
    with _.
      (SR.ones_code_bits k;                           // code_to_bits (2^k-1) k == ones_list k
       SR.round_trip_padded xs k)                     // decode_bits (encode_bits xs @ ones_list k) == Some xs

/// THE CAPSTONE: encode `src` into `enc`, decode the encoded `enc[0..r)` back
/// into `dec`, and recover `src` exactly. A `noextract` proof artifact (it
/// composes the shipped `encode`/`decode` and proves the round-trip; it is not
/// part of the C ABI). `len < 2^24` keeps the encoded length `r` within
/// `decode`'s `< 2^27` domain (`r <= ceil(30*len/8) < 2^27`).
#push-options "--fuel 0 --ifuel 1 --z3rlimit 60"
noextract
val round_trip_c (src enc dec:B.buffer U8.t) (len:U32.t) (out_len:B.buffer U32.t)
  : Stack unit
    (requires fun h ->
      B.live h src /\ B.live h enc /\ B.live h dec /\ B.live h out_len /\
      B.loc_disjoint (B.loc_buffer enc) (B.loc_buffer src) /\
      B.loc_disjoint (B.loc_buffer enc) (MB.loc_buffer huff_len) /\
      B.loc_disjoint (B.loc_buffer enc) (MB.loc_buffer huff_code) /\
      B.loc_disjoint (B.loc_buffer dec) (B.loc_buffer enc) /\
      B.loc_disjoint (B.loc_buffer dec) (B.loc_buffer out_len) /\
      B.loc_disjoint (B.loc_buffer out_len) (B.loc_buffer enc) /\
      B.length src == U32.v len /\ U32.v len < pow2 24 /\
      4 * U32.v len + 1 <= B.length enc /\
      U32.v len <= B.length dec /\ B.length out_len == 1)
    (ensures fun h0 _ h1 ->
      B.modifies (B.loc_union (B.loc_union (B.loc_buffer enc) (B.loc_buffer dec))
                              (B.loc_buffer out_len)) h0 h1 /\
      U32.v (Seq.index (B.as_seq h1 out_len) 0) == U32.v len /\
      RD.decoded_prefix (B.as_seq h1 dec) (U32.v len)
        == RD.decoded_prefix (B.as_seq h0 src) (U32.v len))

noextract
let round_trip_c src enc dec len out_len =
  assert_norm (pow2 24 == 16777216);
  assert_norm (pow2 27 == 134217728);                 (* len < 2^24 < 2^27, so encode/decode apply *)
  let h0 = get () in
  let r = LC.encode src len enc in
  let h_mid = get () in
  (* r <= ceil(30*len/8) < 2^27, so it is a legal decode input length *)
  LC.sum_blen_bound (MB.as_seq h0 huff_len) (B.as_seq h0 src) (U32.v len);
  let decsrc = B.sub enc 0ul r in
  RD.decoded_prefix_length (B.as_seq h0 src) (U32.v len);
  (* discharge decode's accept-hypothesis: decode_bits (bytes_to_bits decsrc) == Some src *)
  round_trip_bridge (B.as_seq h_mid enc) (U32.v r)
                    (RD.decoded_prefix (B.as_seq h0 src) (U32.v len));
  let _ = LD.decode_dfa decsrc r dec len out_len in
  ()
#pop-options
