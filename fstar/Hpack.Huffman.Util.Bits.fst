module Hpack.Huffman.Util.Bits

/// MSB-first bit-string arithmetic, RFC-agnostic.
///
/// A code is a natural `c` read as `l` bits, most-significant bit first. This
/// module defines that reading (`code_to_bits`), its inverse valuation
/// (`value_of`), and the div/mod lemmas relating the two — in particular
/// `value_of_code_prefix`, which pins the value of any prefix of a code's bit
/// string to its top bits. Everything is `Prims.pow2`-based and uses
/// `FStar.Math.Lemmas`, so one power-of-two library is shared across the proof.

open FStar.Mul
module L = FStar.List.Tot
module M = FStar.Math.Lemmas

#set-options "--fuel 1 --ifuel 1 --z3rlimit 40"

(* ---------------------------------------------------------------------- *)
(* Bit strings (MSB first) <-> code values                                *)
(* ---------------------------------------------------------------------- *)

(* `code_to_bits` and `value_of` are the transparent definitions exposed in the
   interface (Hpack.Huffman.Util.Bits.fsti) — visible here. *)

/// `code_to_bits` produces exactly `l` bits.
noextract
let rec length_code_to_bits (c:nat) (l:nat)
  : Lemma (ensures L.length (code_to_bits c l) == l) (decreases l)
  = if l = 0 then () else length_code_to_bits (c % pow2 (l - 1)) (l - 1)

/// One-step unfolding of `code_to_bits` (valid because `l >= 1`).
noextract let code_to_bits_unfold (c:nat) (l:nat{l >= 1})
  : Lemma (code_to_bits c l
           == ((c / pow2 (l - 1)) % 2 = 1) :: code_to_bits (c % pow2 (l - 1)) (l - 1))
  = ()

#push-options "--fuel 2 --ifuel 1 --z3rlimit 80"

/// Appending a bit at the (least-significant) end doubles the value and adds it.
noextract let rec value_of_snoc (pre:list bool) (x:bool)
  : Lemma (ensures value_of (L.append pre [x]) == value_of pre * 2 + (if x then 1 else 0))
          (decreases pre)
  = match pre with
    | [] -> assert_norm (pow2 0 == 1)
    | h :: t ->
      value_of_snoc t x;
      L.append_length t [x];
      M.pow2_double_mult (L.length t)

/// THE BRIDGE: the value of a prefix `pre` of `code_to_bits c l` (with `c`
/// fitting in `l` bits) is the top `length pre` bits of `c`, i.e.
/// `c / 2^(l - length pre)`. All the div/mod arithmetic of decoding lives here,
/// proved once.
noextract let rec value_of_code_prefix (c:nat) (l:nat) (pre suf:list bool)
  : Lemma (requires L.append pre suf == code_to_bits c l /\ c < pow2 l /\ L.length pre <= l)
          (ensures value_of pre == c / pow2 (l - L.length pre))
          (decreases pre)
  = match pre with
    | [] -> M.small_division_lemma_1 c (pow2 l)        // c / pow2 l == 0
    | ph :: ptl ->
      if l = 0 then ()                                   // vacuous: length pre <= l = 0 but pre is cons
      else begin
        code_to_bits_unfold c l;                         // expose code_to_bits c l as bit :: tail
        let m = L.length ptl in
        let q = c / pow2 (l - 1) in
        let r = c % pow2 (l - 1) in
        M.pow2_double_mult (l - 1);                      // pow2 l == 2 * pow2 (l-1)
        value_of_code_prefix r (l - 1) ptl suf;          // IH: value_of ptl == r / pow2 ((l-1)-m)
        M.lemma_div_lt c l (l - 1);                      // q < pow2 1 == 2, so ph contributes q * pow2 m
        assert_norm (pow2 1 == 2);
        calc (==) {
          value_of pre;
          == { (* value_of unfold; ph = (q%2=1) and q<2 give (if ph .. )= q*pow2 m *) }
          q * pow2 m + value_of ptl;
          == { (* IH *) }
          q * pow2 m + r / pow2 (l - 1 - m);
          == { M.pow2_plus m (l - 1 - m);                // pow2(l-1) == pow2 m * pow2(l-1-m)
               M.lemma_div_mod c (pow2 (l - 1));         // c == q*pow2(l-1) + r
               M.lemma_div_plus r (q * pow2 m) (pow2 (l - 1 - m)) }
          c / pow2 (l - 1 - m);
        }
      end

/// Splitting a code's bit string: the `(a+b)`-bit string of `c` is its top `a`
/// bits (`c / 2^b`) followed by its low `b` bits (`c mod 2^b`). The encoder's
/// shift-or append (`a` old bits, `b` new) and `drain`'s byte peel-off (`a = 8`)
/// are both instances. Proved by induction on the high part `a`.
noextract let rec code_to_bits_split (c:nat) (a b:nat)
  : Lemma (requires c < pow2 (a + b))
          (ensures code_to_bits c (a + b)
                   == code_to_bits (c / pow2 b) a @ code_to_bits (c % pow2 b) b)
          (decreases a)
  = if a = 0 then
      M.small_modulo_lemma_1 c (pow2 b)                 // c % pow2 b == c, and code_to_bits _ 0 == []
    else begin
      let n = a - 1 in
      code_to_bits_unfold c (a + b);                    // a + b >= 1
      code_to_bits_unfold (c / pow2 b) a;               // a >= 1
      M.pow2_plus b n;                                  // pow2 b * pow2 n == pow2 (b + n) == pow2 (n + b)
      M.division_multiplication_lemma c (pow2 b) (pow2 n);   // (c / 2^b) / 2^n == c / 2^(n+b)
      M.pow2_modulo_division_lemma_1 c b (n + b);       // (c % 2^(n+b)) / 2^b == (c / 2^b) % 2^n
      M.pow2_modulo_modulo_lemma_1 c b (n + b);         // (c % 2^(n+b)) % 2^b == c % 2^b
      code_to_bits_split (c % pow2 (n + b)) n b          // IH on the (n+b)-bit tail
    end

#pop-options
