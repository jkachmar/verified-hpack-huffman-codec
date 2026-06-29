module Hpack.Huffman.Lowstar.Codec

/// Verified Low* implementation of the HPACK Huffman *encoder* (RFC 7541 §5.2,
/// Appendix B), which KaRaMeL lowers to C.
///
/// `encode_len`/`encode` are proven memory-safe and length-exact (`encode` writes
/// exactly `encode_len` bytes) and content-correct (the output bytes read
/// MSB-first are `Spec.Codec.encode_bits` of the input plus ≤7 padding bits).
/// Decoding lives in `Hpack.Huffman.Lowstar.Dfa` (the verified nibble DFA); the
/// former per-bit `decode_loop`/`find_sym` were removed once it reached parity.

open FStar.HyperStack.ST
open FStar.Mul

module B    = LowStar.Buffer
module MB   = LowStar.Monotonic.Buffer
module IB   = LowStar.ImmutableBuffer
module U8   = FStar.UInt8
module U32  = FStar.UInt32
module U64  = FStar.UInt64
module I32  = FStar.Int32
module HS   = FStar.HyperStack
module Seq  = FStar.Seq
module Cast = FStar.Int.Cast
module M    = FStar.Math.Lemmas
module L    = FStar.List.Tot
module G    = FStar.Ghost
module BS   = Hpack.Huffman.Util.Bits
module SC   = Hpack.Huffman.Spec.Codec
module RD   = Hpack.Huffman.Bridge.Decode
module RE   = Hpack.Huffman.Refine.Encode

open Hpack.Huffman.Lowstar.Tables

#set-options "--fuel 1 --ifuel 1 --z3rlimit 50"

/// The length-table element type: an RFC code length, intrinsically in [5,30].
unfold let lenbits = x:U8.t{5 <= U8.v x /\ U8.v x <= 30}

(* ---------------------------------------------------------------------- *)
(* Ghost specification: total encoded bit-length                          *)
(* ---------------------------------------------------------------------- *)

/// Bit length of byte `b`, per a snapshot `lens` of the length table.
/// (Spec-only: `noextract` keeps it out of the generated C.)
noextract
let blen (lens:Seq.seq lenbits{Seq.length lens == 256}) (b:U8.t)
  : n:nat{5 <= n /\ n <= 30}
  = U8.v (Seq.index lens (U8.v b))

/// Total bits needed to encode the first `i` bytes of `src`.
noextract
let rec sum_blen
  (lens:Seq.seq lenbits{Seq.length lens == 256})
  (src:Seq.seq U8.t)
  (i:nat{i <= Seq.length src})
  : Tot nat (decreases i)
  = if i = 0 then 0
    else sum_blen lens src (i - 1) + blen lens (Seq.index src (i - 1))

/// Each symbol contributes at most 30 bits, so the running total is <= 30*i.
noextract
let rec sum_blen_bound
  (lens:Seq.seq lenbits{Seq.length lens == 256})
  (src:Seq.seq U8.t)
  (i:nat{i <= Seq.length src})
  : Lemma (ensures sum_blen lens src i <= 30 * i) (decreases i)
  = if i = 0 then () else sum_blen_bound lens src (i - 1)

(* ---------------------------------------------------------------------- *)
(* encode_len                                                             *)
(* ---------------------------------------------------------------------- *)

/// Number of bytes the Huffman encoding of `src[0..len)` occupies:
/// ceil(total_bits / 8). Reads only the length table; allocates nothing
/// observable to the caller.
///
/// Precondition `U32.v len < pow2 27` keeps the bit total within U64 and the
/// byte result within U32 (HPACK string literals are far smaller in practice).
///
/// NOTE(shim): KaRaMeL erases this precondition from the generated C, so the
/// hand-written `hpack_huffman_*` shim MUST guard the boundary — reject
/// (or otherwise refuse) `len >= 2^27` before calling in, otherwise a caller
/// passing a huge length hits an unproven uint64->uint32 truncation. HPACK frame
/// sizes cap real inputs well below this, so a guard is belt-and-suspenders.
val encode_len (src:B.buffer U8.t) (len:U32.t)
  : Stack U32.t
    (requires fun h ->
      B.live h src /\ B.length src == U32.v len /\ U32.v len < pow2 27)
    (ensures fun h0 r h1 ->
      B.modifies B.loc_none h0 h1 /\
      U32.v r == (sum_blen (MB.as_seq h0 huff_len) (B.as_seq h0 src) (U32.v len) + 7) / 8)

/// Read-only accumulator: sum the bit-lengths of src[i..len), starting from
/// `acc` = bits already counted for src[0..i). No allocation, so it modifies
/// nothing observable.
val sum_loop (src:B.buffer U8.t) (len:U32.t) (i:U32.t) (acc:U64.t)
  : Stack U64.t
    (requires fun h ->
      B.live h src /\ MB.live h huff_len /\ B.length src == U32.v len /\
      U32.v i <= U32.v len /\ U32.v len < pow2 27 /\
      U64.v acc == sum_blen (MB.as_seq h huff_len) (B.as_seq h src) (U32.v i))
    (ensures fun h0 r h1 ->
      B.modifies B.loc_none h0 h1 /\
      U64.v r == sum_blen (MB.as_seq h0 huff_len) (B.as_seq h0 src) (U32.v len))
    (decreases (U32.v len - U32.v i))

let rec sum_loop src len i acc =
  if U32.eq i len then acc
  else begin
    let h = get () in
    let b = B.index src i in
    let l = B.index huff_len (Cast.uint8_to_uint32 b) in
    sum_blen_bound (MB.as_seq h huff_len) (B.as_seq h src) (U32.v i);
    let acc' = U64.add acc (Cast.uint8_to_uint64 l) in
    sum_loop src len (U32.add i 1ul) acc'
  end

let encode_len src len =
  B.recall huff_len;
  let t = sum_loop src len 0ul 0uL in
  let h = get () in
  sum_blen_bound (MB.as_seq h huff_len) (B.as_seq h src) (U32.v len);
  (* t <= 30*len < 2^32, so (t+7)/8 fits in U32 and the cast is exact *)
  assert_norm (pow2 27 == 134217728);
  assert_norm (pow2 32 == 4294967296);
  let bytes = U64.div (U64.add t 7uL) 8uL in
  Cast.uint64_to_uint32 bytes

(* ---------------------------------------------------------------------- *)
(* encode                                                                 *)
(* ---------------------------------------------------------------------- *)

/// Flush whole buffered bytes (MSB-first). Preserves `8*out + nbits`, leaves
/// `nbits < 8`, and — the content guarantee — the `nbits/8` bytes it appends are
/// exactly the top of the `nbits`-bit accumulator window: their bits are
/// `code_to_bits (bits / 2^residual) (8 * nbytes)`. Returns the advanced write
/// index and the residual nbits.
///
/// Non-recursive (emits exactly `nbits/8` bytes via a counted loop) and
/// `inline_for_extraction`, so KaRaMeL folds it into the caller's loop body
/// rather than emitting a per-symbol function call. `private` keeps it
/// module-local so KaRaMeL drops the (now-unreferenced) standalone definition
/// instead of emitting it as dead code.
private inline_for_extraction
val drain (dst:B.buffer U8.t) (len:U32.t) (out:U32.t) (nbits:U32.t) (bits:U64.t)
  : Stack (U32.t & U32.t)
    (requires fun h ->
      B.live h dst /\
      U32.v len < pow2 27 /\ 4 * U32.v len + 1 <= B.length dst /\
      U32.v nbits < 64 /\ U64.v bits < pow2 (U32.v nbits) /\
      8 * U32.v out + U32.v nbits <= 30 * U32.v len)
    (ensures fun h0 res h1 ->
      B.modifies (B.loc_buffer dst) h0 h1 /\ B.live h1 dst /\
      U32.v (snd res) < 8 /\
      8 * U32.v (fst res) + U32.v (snd res) == 8 * U32.v out + U32.v nbits /\
      U32.v (fst res) <= B.length dst /\
      RE.enc_bits (B.as_seq h1 dst) (U32.v (fst res)) ==
        RE.enc_bits (B.as_seq h0 dst) (U32.v out)
        @ BS.code_to_bits (U64.v bits / pow2 (U32.v (snd res)))
                          (8 * U32.v (fst res) - 8 * U32.v out))

#push-options "--fuel 1 --ifuel 1 --z3rlimit 50"
private inline_for_extraction
let drain dst len out nbits bits =
  let nbytes = U32.div nbits 8ul in
  (* 8*nbytes <= nbits and 8*out+nbits <= 30*len <= 32*len  ==>  out+nbytes <= 4*len <= length dst *)
  assert (8 * U32.v nbytes <= U32.v nbits);
  assert (8 * (U32.v out + U32.v nbytes) <= 32 * U32.v len);
  assert (U32.v out + U32.v nbytes <= B.length dst);
  let h0 = get () in
  let inv (h:HS.mem) (j:nat) : Type0 =
    j <= U32.v nbytes /\
    B.live h dst /\
    B.modifies (B.loc_buffer dst) h0 h /\
    U32.v out + U32.v nbytes <= B.length dst /\
    RE.enc_bits (B.as_seq h dst) (U32.v out + j) ==
      RE.enc_bits (B.as_seq h0 dst) (U32.v out)
      @ BS.code_to_bits (U64.v bits / pow2 (U32.v nbits - 8 * j)) (8 * j)
  in
  let body (j:U32.t{0 <= U32.v j /\ U32.v j < U32.v nbytes})
    : Stack unit
      (requires fun h -> inv h (U32.v j))
      (ensures fun h1 _ h2 -> inv h1 (U32.v j) /\ inv h2 (U32.v j + 1))
    = (* j < nbytes ==> 8*(j+1) <= 8*nbytes <= nbits, so the shift is in [0,64) *)
      let shift = U32.sub nbits (U32.mul 8ul (U32.add j 1ul)) in
      let h1 = get () in
      [@inline_let] let byte = Cast.uint64_to_uint8 (U64.shift_right bits shift) in   (* U8.v == (bits / 2^shift) % 256 *)
      B.upd dst (U32.add out j) byte;
      (* the freshly written byte is the next 8 bits down from the window's top *)
      RE.enc_bits_upd_snoc (B.as_seq h1 dst) (U32.v out + U32.v j) byte;
      M.lemma_div_lt (U64.v bits) (U32.v nbits) (U32.v shift);          (* bits / 2^shift < 2^(8*(j+1)) *)
      M.division_multiplication_lemma (U64.v bits) (pow2 (U32.v shift)) (pow2 8);
      M.pow2_plus (U32.v shift) 8;                                      (* (bits/2^shift)/2^8 == bits/2^(shift+8) *)
      BS.code_to_bits_split (U64.v bits / pow2 (U32.v shift)) (8 * U32.v j) 8;
      L.append_assoc (RE.enc_bits (B.as_seq h0 dst) (U32.v out))        (* re-associate top-bits @ new byte *)
                     (BS.code_to_bits (U64.v bits / pow2 (U32.v nbits - 8 * U32.v j)) (8 * U32.v j))
                     (BS.code_to_bits (U8.v byte) 8)
  in
  BS.length_code_to_bits (U64.v bits / pow2 (U32.v nbits)) 0;
  L.append_l_nil (RE.enc_bits (B.as_seq h0 dst) (U32.v out));          (* inv h0 0 *)
  C.Loops.for 0ul nbytes inv body;
  (U32.add out nbytes, U32.sub nbits (U32.mul nbytes 8ul))
#pop-options

/// Encode src[i..len): for each byte, append its code to the bit accumulator and
/// flush whole bytes. Maintains nbits < 8, the bit total `8*out + nbits ==
/// sum_blen ... i`, the residual fits (`bits < 2^nbits`), and — the content
/// guarantee — the emitted bytes plus the residual are exactly the RFC bit stream
/// of the input so far: `enc_bits dst out @ code_to_bits bits nbits == encode_bits
/// (decoded_prefix gsrc i)`. `gsrc` is the fixed (ghost) input sequence, pinned to
/// `src`, so the invariant is stable across the recursion. Returns (out, nbits, bits).
val encode_loop
  (dst src:B.buffer U8.t) (len i out nbits:U32.t) (bits:U64.t)
  (gsrc:G.erased (Seq.seq U8.t))
  : Stack (U32.t & U32.t & U64.t)
    (requires fun h ->
      B.live h dst /\ B.live h src /\ MB.live h huff_len /\ MB.live h huff_code /\
      B.loc_disjoint (B.loc_buffer dst) (B.loc_buffer src) /\
      B.loc_disjoint (B.loc_buffer dst) (MB.loc_buffer huff_len) /\
      B.loc_disjoint (B.loc_buffer dst) (MB.loc_buffer huff_code) /\
      B.length src == U32.v len /\ U32.v len < pow2 27 /\
      4 * U32.v len + 1 <= B.length dst /\
      U32.v i <= U32.v len /\ U32.v nbits < 8 /\
      G.reveal gsrc == B.as_seq h src /\
      U64.v bits < pow2 (U32.v nbits) /\
      U32.v out <= B.length dst /\
      8 * U32.v out + U32.v nbits ==
        sum_blen (MB.as_seq h huff_len) (G.reveal gsrc) (U32.v i) /\
      RE.enc_bits (B.as_seq h dst) (U32.v out) @ BS.code_to_bits (U64.v bits) (U32.v nbits)
        == SC.encode_bits (RD.decoded_prefix (G.reveal gsrc) (U32.v i)))
    (ensures fun h0 res h1 ->
      B.modifies (B.loc_buffer dst) h0 h1 /\ B.live h1 dst /\
      (let (o, n, bb) = res in
        U32.v n < 8 /\ U64.v bb < pow2 (U32.v n) /\
        U32.v o <= B.length dst /\
        8 * U32.v o + U32.v n ==
          sum_blen (MB.as_seq h0 huff_len) (G.reveal gsrc) (U32.v len) /\
        RE.enc_bits (B.as_seq h1 dst) (U32.v o) @ BS.code_to_bits (U64.v bb) (U32.v n)
          == SC.encode_bits (RD.decoded_prefix (G.reveal gsrc) (U32.v len))))
    (decreases (U32.v len - U32.v i))

#push-options "--fuel 1 --ifuel 1 --z3rlimit 100"
let rec encode_loop dst src len i out nbits bits gsrc =
  if U32.eq i len then (out, nbits, bits)
  else begin
    let h = get () in
    let b = B.index src i in
    let code = B.index huff_code (Cast.uint8_to_uint32 b) in
    let cb = B.index huff_len (Cast.uint8_to_uint32 b) in
    let cb32 = Cast.uint8_to_uint32 cb in
    (* relate the table reads to the spec code / length for byte `b` *)
    IB.recall_contents huff_code huff_code_contents;
    IB.recall_contents huff_len huff_len_contents;
    RE.huff_code_correct (U8.v b);                  (* U32.v code == code_of (U8.v b) *)
    RE.huff_len_correct (U8.v b);                   (* U8.v cb   == len_of  (U8.v b) *)
    RE.code_fits (U8.v b);                           (* code_of (U8.v b) < pow2 (len_of (U8.v b)) *)
    (* sum_blen i <= 30*i, so the post-symbol total stays <= 30*(i+1) <= 30*len *)
    sum_blen_bound (MB.as_seq h huff_len) (G.reveal gsrc) (U32.v i);
    (* the shift-or appends the code below the residual: bits1 == bits*2^cb + code *)
    M.pow2_plus (U32.v nbits) (U32.v cb32);          (* pow2 nbits * pow2 cb == pow2 (nbits+cb) *)
    M.lemma_mult_lt_right (pow2 (U32.v cb32)) (U64.v bits) (pow2 (U32.v nbits));
    M.pow2_lt_compat 64 (U32.v nbits + U32.v cb32);  (* bits*2^cb < pow2(nbits+cb) < pow2 64 *)
    M.small_mod (U64.v bits * pow2 (U32.v cb32)) (pow2 64);          (* shift_left exact: no wrap *)
    let bits1 = U64.logor (U64.shift_left bits cb32) (Cast.uint32_to_uint64 code) in
    let nbits1 = U32.add nbits cb32 in
    M.multiple_modulo_lemma (U64.v bits) (pow2 (U32.v cb32));        (* (bits*2^cb) % 2^cb == 0 *)
    FStar.UInt.logor_disjoint #64 (U64.v bits * pow2 (U32.v cb32)) (U32.v code) (U32.v cb32);
    assert (U64.v bits1 == U64.v bits * pow2 (U32.v cb32) + U32.v code);  (* shift-or == multiply-add *)
    M.lemma_mult_le_right (pow2 (U32.v cb32)) (U64.v bits + 1) (pow2 (U32.v nbits));
    assert (U64.v bits1 < pow2 (U32.v nbits1));                      (* (bits+1)*2^cb <= 2^(nbits+cb) *)
    M.lemma_div_plus (U32.v code) (U64.v bits) (pow2 (U32.v cb32));  (* bits1 / 2^cb == bits *)
    M.lemma_mod_plus (U32.v code) (U64.v bits) (pow2 (U32.v cb32)); (* bits1 % 2^cb == code *)
    M.small_mod (U32.v code) (pow2 (U32.v cb32));
    BS.code_to_bits_split (U64.v bits1) (U32.v nbits) (U32.v cb32);  (* split bits1 into bits ++ code *)
    (* fold the appended code into the spec output: encode_bits decoded_prefix (i+1) *)
    L.append_assoc (RE.enc_bits (B.as_seq h dst) (U32.v out))
                   (BS.code_to_bits (U64.v bits) (U32.v nbits))
                   (BS.code_to_bits (U32.v code) (U32.v cb32));
    RE.encode_bits_snoc (RD.decoded_prefix (G.reveal gsrc) (U32.v i)) (U8.v b);
    let res = drain dst len out nbits1 bits1 in
    let out2 = fst res in
    let nbits2 = snd res in
    assert (U32.v nbits2 < 8);
    let h2 = get () in
    (* dst writes don't touch src/huff_len/huff_code, so their snapshots are stable *)
    MB.modifies_buffer_elim huff_len (B.loc_buffer dst) h h2;
    MB.modifies_buffer_elim huff_code (B.loc_buffer dst) h h2;
    MB.modifies_buffer_elim src (B.loc_buffer dst) h h2;
    (* 1 <= 2^nbits2 < 2^64, so (1<<nbits2)-1 does not underflow *)
    FStar.Math.Lemmas.pow2_lt_compat 64 (U32.v nbits2);
    FStar.Math.Lemmas.pow2_le_compat (U32.v nbits2) 0;
    let mask = U64.sub (U64.shift_left 1uL nbits2) 1uL in
    let bits2 = U64.logand bits1 mask in
    assert_norm (pow2 0 == 1);
    M.small_mod (pow2 (U32.v nbits2)) (pow2 64);                      (* 1 << nbits2 == pow2 nbits2, so mask == 2^nbits2 - 1 *)
    (if U32.v nbits2 = 0
     then FStar.UInt.logand_lemma_1 #64 (U64.v bits1)                 (* mask == 0, so bits2 == 0 == bits1 % 1 *)
     else FStar.UInt.logand_mask #64 (U64.v bits1) (U32.v nbits2));   (* bits2 == bits1 % 2^nbits2 *)
    assert (U64.v bits2 == U64.v bits1 % pow2 (U32.v nbits2));
    (* the drained bytes ++ new residual reconstitute bits1's nbits1 bits *)
    BS.code_to_bits_split (U64.v bits1) (8 * U32.v out2 - 8 * U32.v out) (U32.v nbits2);
    L.append_assoc (RE.enc_bits (B.as_seq h dst) (U32.v out))
                   (BS.code_to_bits (U64.v bits1 / pow2 (U32.v nbits2)) (8 * U32.v out2 - 8 * U32.v out))
                   (BS.code_to_bits (U64.v bits2) (U32.v nbits2));
    encode_loop dst src len (U32.add i 1ul) out2 nbits2 bits2 gsrc
  end
#pop-options

/// Huffman-encode `src[0..len)` into `dst`, returning the number of bytes
/// written. Proven memory-safe and length-exact (`r == encode_len src len`), and
/// — the content guarantee — the emitted bytes are exactly the RFC bit stream of
/// the input followed by ≤ 7 all-ones padding bits to the next byte boundary:
/// `enc_bits dst r == encode_bits (input bytes) @ code_to_bits (2^k - 1) k` for
/// some `k <= 7`. (`code_to_bits (2^k - 1) k` is `k` all-ones bits; `Spec.RoundTrip`
/// ties that to the padded round-trip.)
val encode (src:B.buffer U8.t) (len:U32.t) (dst:B.buffer U8.t)
  : Stack U32.t
    (requires fun h ->
      B.live h src /\ B.live h dst /\
      B.loc_disjoint (B.loc_buffer dst) (B.loc_buffer src) /\
      B.loc_disjoint (B.loc_buffer dst) (MB.loc_buffer huff_len) /\
      B.loc_disjoint (B.loc_buffer dst) (MB.loc_buffer huff_code) /\
      B.length src == U32.v len /\ U32.v len < pow2 27 /\
      4 * U32.v len + 1 <= B.length dst)
    (ensures fun h0 r h1 ->
      B.modifies (B.loc_buffer dst) h0 h1 /\
      U32.v r ==
        (sum_blen (MB.as_seq h0 huff_len) (B.as_seq h0 src) (U32.v len) + 7) / 8 /\
      U32.v r <= B.length dst /\
      (exists (k:nat). k <= 7 /\
         RE.enc_bits (B.as_seq h1 dst) (U32.v r) ==
           SC.encode_bits (RD.decoded_prefix (B.as_seq h0 src) (U32.v len))
           @ BS.code_to_bits (pow2 k - 1) k))

#push-options "--fuel 1 --ifuel 1 --z3rlimit 50"
let encode src len dst =
  B.recall huff_len;
  B.recall huff_code;
  let h0 = get () in
  assert_norm (pow2 0 == 1);
  let gsrc0 : G.erased (Seq.seq U8.t) = G.hide (B.as_seq h0 src) in
  let res = encode_loop dst src len 0ul 0ul 0ul 0uL gsrc0 in
  let out = (let (o, _, _) = res in o) in
  let nbits = (let (_, n, _) = res in n) in
  let bits = (let (_, _, bb) = res in bb) in
  let h1 = get () in
  MB.modifies_buffer_elim huff_len (B.loc_buffer dst) h0 h1;
  MB.modifies_buffer_elim src (B.loc_buffer dst) h0 h1;
  sum_blen_bound (MB.as_seq h0 huff_len) (B.as_seq h0 src) (U32.v len);
  assert_norm (pow2 27 == 134217728);
  if U32.gt nbits 0ul then begin
    let pad = U32.sub 8ul nbits in
    M.pow2_lt_compat 64 (U32.v pad);
    M.pow2_le_compat (U32.v pad) 0;
    let ones = U64.sub (U64.shift_left 1uL pad) 1uL in
    M.small_mod (pow2 (U32.v pad)) (pow2 64);        (* U64.v ones == 2^pad - 1 *)
    (* the final byte is [residual nbits bits][pad all-ones bits] *)
    M.pow2_plus (U32.v nbits) (U32.v pad);           (* 2^nbits * 2^pad == 2^8 *)
    assert_norm (pow2 8 == 256);
    M.pow2_lt_compat 64 (U32.v nbits + U32.v pad);
    M.small_mod (U64.v bits * pow2 (U32.v pad)) (pow2 64);   (* shift_left exact *)
    [@inline_let] let byte64 = U64.logor (U64.shift_left bits pad) ones in
    M.multiple_modulo_lemma (U64.v bits) (pow2 (U32.v pad));
    FStar.UInt.logor_disjoint #64 (U64.v bits * pow2 (U32.v pad)) (U64.v ones) (U32.v pad);
    M.lemma_mult_le_right (pow2 (U32.v pad)) (U64.v bits + 1) (pow2 (U32.v nbits));
    assert (U64.v byte64 == U64.v bits * pow2 (U32.v pad) + (pow2 (U32.v pad) - 1));
    assert (U64.v byte64 < pow2 8);
    let byte = Cast.uint64_to_uint8 byte64 in
    M.small_mod (U64.v byte64) (pow2 8);             (* U8.v byte == U64.v byte64 *)
    (* split the byte: top nbits == bits, low pad == 2^pad - 1 *)
    M.small_division_lemma_1 (U64.v ones) (pow2 (U32.v pad));
    M.lemma_div_plus (U64.v ones) (U64.v bits) (pow2 (U32.v pad));   (* byte / 2^pad == bits *)
    M.lemma_mod_plus (U64.v ones) (U64.v bits) (pow2 (U32.v pad));   (* byte % 2^pad == ones *)
    M.small_mod (U64.v ones) (pow2 (U32.v pad));
    BS.code_to_bits_split (U8.v byte) (U32.v nbits) (U32.v pad);
    assert (8 * U32.v out < 32 * U32.v len);   (* out < 4*len < length dst *)
    B.upd dst out byte;
    let h2 = get () in
    RE.enc_bits_upd_snoc (B.as_seq h1 dst) (U32.v out) byte;
    L.append_assoc (RE.enc_bits (B.as_seq h1 dst) (U32.v out))
                   (BS.code_to_bits (U64.v bits) (U32.v nbits))
                   (BS.code_to_bits (pow2 (U32.v pad) - 1) (U32.v pad));
    introduce exists (k:nat). (k <= 7 /\
        RE.enc_bits (B.as_seq h2 dst) (U32.v out + 1) ==
          SC.encode_bits (RD.decoded_prefix (B.as_seq h0 src) (U32.v len))
          @ BS.code_to_bits (pow2 k - 1) k)
    with (U32.v pad) and ();
    U32.add out 1ul
  end else begin
    (* total bits already byte-aligned: no padding (k = 0, an empty all-ones run) *)
    L.append_l_nil (SC.encode_bits (RD.decoded_prefix (B.as_seq h0 src) (U32.v len)));
    L.append_l_nil (RE.enc_bits (B.as_seq h1 dst) (U32.v out));   (* drop the empty residual *)
    introduce exists (k:nat). (k <= 7 /\
        RE.enc_bits (B.as_seq h1 dst) (U32.v out) ==
          SC.encode_bits (RD.decoded_prefix (B.as_seq h0 src) (U32.v len))
          @ BS.code_to_bits (pow2 k - 1) k)
    with 0 and ();
    out
  end
#pop-options
