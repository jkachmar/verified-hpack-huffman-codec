module Hpack.Huffman.Spec.RoundTrip

/// The Huffman round-trip theorem: decoding the (unpadded) encoding of a byte
/// string returns that byte string.
///
/// `round_trip : decode_bits (encode_bits bs) == Some bs`.
///
/// The induction is `decode_one` (decoding one symbol's code bits emits that
/// symbol and continues), itself proved by `decode_prefix`, which walks the code
/// bit-by-bit: each proper prefix value misses the table (`no_proper_prefix`) and
/// the full code matches (`lookup_correct`), with the accumulator's value at each
/// step pinned by `value_of_code_prefix`.

open Hpack.Huffman.Table
open Hpack.Huffman.Util.Bits
open Hpack.Huffman.Spec.Codec
open Hpack.Huffman.Spec.Lookup
open FStar.Mul
module L = FStar.List.Tot
module M = FStar.Math.Lemmas
module P = Hpack.Huffman.Table.Properties
module Lst = Hpack.Huffman.Util.List

#set-options "--fuel 1 --ifuel 1 --z3rlimit 40"

(* ---------------------------------------------------------------------- *)
(* Decode induction: decoding a codeword's bits emits its symbol           *)
(* ---------------------------------------------------------------------- *)

#push-options "--fuel 2 --ifuel 1 --z3rlimit 150"

/// One-step unfolding of `decode_go` on a cons input (true by definition).
noextract let decode_go_cons (bhd:bool) (btl:list bool) (acc nbits:nat) (out:list byte)
  : Lemma (decode_go (bhd :: btl) acc nbits out ==
           (let acc' = acc * 2 + (if bhd then 1 else 0) in
            match lookup_v acc' (nbits + 1) with
            | Some s -> if s = eos_index then None else decode_go btl 0 0 (out @ [s])
            | None -> decode_go btl acc' (nbits + 1) out)) = ()

/// Decode the suffix `suf` of `b`'s codeword, given the already-consumed prefix
/// `pre` is in the accumulator (value `value_of pre`, `length pre` bits). Induct
/// on `suf` so `decode_go` unfolds naturally; the accumulator's value at each step
/// is pinned by `value_of_code_prefix`, so proper prefixes miss (`no_proper_prefix`)
/// and the full code matches (`lookup_correct`).
noextract let rec decode_prefix (b:byte) (pre suf rest : list bool) (out:list byte)
  : Lemma (requires (pre @ suf == code_to_bits (code_of b) (len_of b)) /\
                    Cons? suf /\ L.length pre < len_of b)
          (ensures decode_go (suf @ rest) (value_of pre) (L.length pre) out
                   == decode_go rest 0 0 (out @ [b]))
          (decreases suf)
  = P.lemma_table_complete (); P.lemma_all_fit ();
    Lst.all_pred_index P.fits hpack_table b;            // code_of b < pow2 (len_of b)
    let cb = code_of b in
    let lb = len_of b in
    L.append_length pre suf;                            // length pre + length suf == lb
    length_code_to_bits cb lb;                          //   (= length of the full code)
    match suf with
    | bhd :: stl ->
      let pre' = pre @ [bhd] in
      L.append_assoc pre [bhd] stl;                     // pre' @ stl == pre @ suf == full
      L.append_length pre [bhd];                        // length pre' == length pre + 1
      value_of_code_prefix cb lb pre suf;               // value_of pre  == cb / pow2 (lb - length pre)
      value_of_code_prefix cb lb pre' stl;              // value_of pre' == cb / pow2 (lb - length pre')
      value_of_snoc pre bhd;                            // value_of pre' == value_of pre * 2 + bhd
      decode_go_cons bhd (stl @ rest) (value_of pre) (L.length pre) out;
      if L.length pre + 1 = lb then begin
        assert_norm (pow2 0 == 1);                      // value_of pre' == cb
        lookup_correct b                                // lookup_v cb lb == Some b ; stl == []
      end
      else begin
        no_proper_prefix b (L.length pre + 1);          // lookup_v (value_of pre') (length pre') == None
        decode_prefix b pre' stl rest out               // IH on the shorter suffix
      end

#pop-options

/// Decoding `b`'s full code bits (followed by `rest`) emits `b`, then continues.
noextract let decode_one (b:byte) (rest:list bool) (out:list byte)
  : Lemma (decode_go (code_to_bits (code_of b) (len_of b) @ rest) 0 0 out
           == decode_go rest 0 0 (out @ [b]))
  = P.lemma_table_complete (); P.lemma_all_pos ();
    Lst.all_pred_index P.pos_len hpack_table b;         // len_of b >= 1
    code_to_bits_unfold (code_of b) (len_of b);         // full code is a cons
    decode_prefix b [] (code_to_bits (code_of b) (len_of b)) rest out

(* ---------------------------------------------------------------------- *)
(* Round-trip                                                              *)
(* ---------------------------------------------------------------------- *)

/// `code_bits_of b == code_to_bits (code_of b) (len_of b)` (just unfolds defs).
noextract let code_bits_eq (b:byte)
  : Lemma (code_bits_of b == code_to_bits (code_of b) (len_of b)) = ()

#push-options "--fuel 2 --ifuel 1 --z3rlimit 60"
noextract let rec round_trip_go (bs:list byte) (out:list byte)
  : Lemma (ensures decode_go (encode_bits bs) 0 0 out == Some (out @ bs))
          (decreases bs)
  = match bs with
    | [] -> assert_norm (pow2 0 == 1); L.append_l_nil out
    | b :: tl ->
        code_bits_eq b;     // encode_bits (b::tl) == code_to_bits (code b)(len b) @ encode_bits tl
        assert (encode_bits (b :: tl) == code_to_bits (code_of b) (len_of b) @ encode_bits tl);
        decode_one b (encode_bits tl) out;
        round_trip_go tl (out @ [b]);
        L.append_assoc out [b] tl
#pop-options

/// THE ROUND-TRIP: decoding the (unpadded) encoding of `bs` returns `bs`.
noextract let round_trip (bs:list byte)
  : Lemma (decode_bits (encode_bits bs) == Some bs)
  = round_trip_go bs []

(* ---------------------------------------------------------------------- *)
(* Padded round-trip                                                       *)
(*                                                                         *)
(* The real (byte-oriented) decoder sees the unpadded code stream followed *)
(* by <= 7 all-ones padding bits to the next byte boundary. We extend the  *)
(* round-trip across that padding: each padding bit forms an all-ones      *)
(* value that is a proper prefix of the EOS code, so it matches no         *)
(* codeword, and the residual passes `valid_padding_v`.                    *)
(* ---------------------------------------------------------------------- *)

/// The codeword stream followed by an arbitrary suffix `rest`: decoding it
/// emits `bs` and then continues decoding `rest`. (Generalises `round_trip_go`
/// with a trailing remainder; the padding tail is one such remainder.)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 60"
noextract let rec round_trip_go_rest (bs:list byte) (rest:list bool) (out:list byte)
  : Lemma (ensures decode_go (encode_bits bs @ rest) 0 0 out
                   == decode_go rest 0 0 (out @ bs))
          (decreases bs)
  = match bs with
    | [] -> L.append_l_nil out          // encode_bits [] @ rest == rest ; out @ [] == out
    | b :: tl ->
        code_bits_eq b;
        // encode_bits (b::tl) @ rest == code_to_bits (code b)(len b) @ (encode_bits tl @ rest)
        L.append_assoc (code_to_bits (code_of b) (len_of b)) (encode_bits tl) rest;
        decode_one b (encode_bits tl @ rest) out;
        round_trip_go_rest tl rest (out @ [b]);
        L.append_assoc out [b] tl
#pop-options

/// `pow2 30 - 1` (the all-ones EOS code) has top-`m`-bits value `pow2 m - 1`:
/// dividing by `pow2 (30 - m)` drops the low `30 - m` (all-ones) bits.
#push-options "--fuel 1 --ifuel 1 --z3rlimit 80"
noextract let eos_prefix_value (m:nat{m <= 30})
  : Lemma ((pow2 30 - 1) / pow2 (30 - m) == pow2 m - 1)
  = let d = 30 - m in
    M.pow2_plus m d;                                   // pow2 30 == pow2 m * pow2 d
    M.pow2_le_compat d 0;                              // 1 <= pow2 d
    M.distributivity_sub_left (pow2 m) 1 (pow2 d);     // (pow2 m - 1)*pow2 d == pow2 m*pow2 d - pow2 d
    assert (pow2 30 - 1 == (pow2 d - 1) + (pow2 m - 1) * pow2 d);
    M.lemma_div_plus (pow2 d - 1) (pow2 m - 1) (pow2 d);
    M.small_division_lemma_1 (pow2 d - 1) (pow2 d)
#pop-options

/// No codeword is an `m`-bit run of ones (`1 <= m < 30`): such a value is a
/// proper prefix of the EOS code, so prefix-freeness rules it out.
noextract let padding_no_match (m:nat{1 <= m /\ m < 30})
  : Lemma (lookup_v (pow2 m - 1) m == None)
  = assert_norm (pow2 30 == 1073741824);
    assert_norm (code_of eos_index == 1073741823);
    assert_norm (len_of eos_index == 30);
    eos_prefix_value m;                  // (pow2 30 - 1) / pow2 (30 - m) == pow2 m - 1
    no_proper_prefix eos_index m         // lookup_v (code eos / pow2 (len eos - m)) m == None

/// `j` all-ones padding bits.
noextract let rec ones_list (j:nat) : list bool =
  if j = 0 then [] else true :: ones_list (j - 1)

/// Decoding `j` all-ones padding bits from an all-ones accumulator (value
/// `pow2 nbits - 1`, `nbits` bits) leaves the output untouched and accepts,
/// provided the total padding stays within the 7-bit budget. Each bit grows the
/// run of ones, which `padding_no_match` shows matches no codeword; at end of
/// input the residual is valid padding.
#push-options "--fuel 2 --ifuel 1 --z3rlimit 60"
noextract let rec decode_pad (j nbits:nat) (out:list byte)
  : Lemma (requires nbits + j <= 7)
          (ensures decode_go (ones_list j) (pow2 nbits - 1) nbits out == Some out)
          (decreases j)
  = M.pow2_le_compat nbits 0;            // 1 <= pow2 nbits, so pow2 nbits - 1 >= 0
    if j = 0 then ()                     // [] : valid_padding_v (pow2 nbits - 1) nbits, nbits <= 7
    else begin
      M.pow2_double_mult nbits;          // pow2 (nbits+1) == 2 * pow2 nbits
      decode_go_cons true (ones_list (j - 1)) (pow2 nbits - 1) nbits out;
      // acc' == (pow2 nbits - 1)*2 + 1 == pow2 (nbits+1) - 1
      padding_no_match (nbits + 1);      // lookup_v (pow2 (nbits+1) - 1) (nbits+1) == None
      decode_pad (j - 1) (nbits + 1) out
    end
#pop-options

/// THE PADDED ROUND-TRIP: decoding the encoding of `bs` followed by `k <= 7`
/// all-ones padding bits returns `bs`. This is the form the byte-oriented
/// decoder actually faces.
noextract let round_trip_padded (bs:list byte) (k:nat{k <= 7})
  : Lemma (decode_go (encode_bits bs @ ones_list k) 0 0 [] == Some bs)
  = assert_norm (pow2 0 == 1);           // pow2 0 - 1 == 0 == the initial accumulator
    round_trip_go_rest bs (ones_list k) [];   // == decode_go (ones_list k) 0 0 ([] @ bs)
    L.append_nil_l bs;                         // [] @ bs == bs
    decode_pad k 0 bs                          // decode_go (ones_list k) 0 0 bs == Some bs

/// `k` all-ones bits, as a code, *are* `ones_list k` — bridging the encoder's
/// padding form (`code_to_bits (2^k - 1) k`, what `encode`'s `ensures` produces)
/// to the spec's `ones_list k` that `round_trip_padded` consumes.
#push-options "--fuel 2 --ifuel 1 --z3rlimit 40"
noextract let rec ones_code_bits (k:nat)
  : Lemma (ensures code_to_bits (pow2 k - 1) k == ones_list k) (decreases k)
  = if k = 0 then ()
    else begin
      let n = k - 1 in
      M.pow2_le_compat n 0;                       // 1 <= pow2 n, so pow2 n - 1 is a nat
      M.pow2_double_mult n;                       // pow2 k == 2 * pow2 n
      M.small_division_lemma_1 (pow2 n - 1) (pow2 n);   // (pow2 n - 1) / pow2 n == 0
      M.lemma_div_plus (pow2 n - 1) 1 (pow2 n);   // (pow2 k - 1) / pow2 n == 1
      M.lemma_mod_plus (pow2 n - 1) 1 (pow2 n);   // (pow2 k - 1) % pow2 n == (pow2 n - 1) % pow2 n
      M.small_mod (pow2 n - 1) (pow2 n);          // (pow2 n - 1) % pow2 n == pow2 n - 1
      code_to_bits_unfold (pow2 k - 1) k;         // head == ((pow2 k - 1)/pow2 n)%2 == 1, tail on pow2 n - 1
      ones_code_bits n
    end
#pop-options
