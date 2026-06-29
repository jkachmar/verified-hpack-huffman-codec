module Hpack.Huffman.Util.Bits

/// MSB-first bit-string arithmetic, RFC-agnostic. A code is a natural `c` read as
/// `l` bits, most-significant first. Exposed transparently: that reading
/// (`code_to_bits`) and its valuation (`value_of`), since spec/refinement
/// definitions are stated in terms of them. The div/mod lemmas relating the two —
/// in particular `value_of_code_prefix` (a code prefix's value is its top bits)
/// and `code_to_bits_split` (an `(a+b)`-bit code splits into its top `a` ∥ low `b`
/// bits) — are exposed as `val`s with their proofs sealed.

open FStar.Mul
module L = FStar.List.Tot

/// The `l`-bit big-endian bit string of `c` (most significant bit first).
noextract
let rec code_to_bits (c:nat) (l:nat) : Tot (list bool) (decreases l) =
  if l = 0 then []
  else ((c / pow2 (l - 1)) % 2 = 1) :: code_to_bits (c % pow2 (l - 1)) (l - 1)

/// The natural number a bit string denotes (MSB first).
noextract
let rec value_of (bl:list bool) : Tot nat =
  match bl with
  | [] -> 0
  | b :: tl -> (if b then pow2 (L.length tl) else 0) + value_of tl

/// `code_to_bits` produces exactly `l` bits.
noextract val length_code_to_bits (c:nat) (l:nat)
  : Lemma (L.length (code_to_bits c l) == l)

/// One-step unfolding of `code_to_bits` (valid because `l >= 1`).
noextract val code_to_bits_unfold (c:nat) (l:nat{l >= 1})
  : Lemma (code_to_bits c l
           == ((c / pow2 (l - 1)) % 2 = 1) :: code_to_bits (c % pow2 (l - 1)) (l - 1))

/// Appending a bit at the (least-significant) end doubles the value and adds it.
noextract val value_of_snoc (pre:list bool) (x:bool)
  : Lemma (value_of (L.append pre [x]) == value_of pre * 2 + (if x then 1 else 0))

/// THE BRIDGE: the value of a prefix `pre` of `code_to_bits c l` (with `c` fitting
/// in `l` bits) is the top `length pre` bits of `c`, i.e. `c / 2^(l - length pre)`.
noextract val value_of_code_prefix (c:nat) (l:nat) (pre suf:list bool)
  : Lemma (requires L.append pre suf == code_to_bits c l /\ c < pow2 l /\ L.length pre <= l)
          (ensures value_of pre == c / pow2 (l - L.length pre))

/// Splitting a code's bit string: the `(a+b)`-bit string of `c` is its top `a`
/// bits (`c / 2^b`) followed by its low `b` bits (`c mod 2^b`). The encoder's
/// shift-or append (`a` old bits, `b` new) and `drain`'s byte peel-off (`a = 8`)
/// are both instances.
noextract val code_to_bits_split (c:nat) (a b:nat)
  : Lemma (requires c < pow2 (a + b))
          (ensures code_to_bits c (a + b)
                   == code_to_bits (c / pow2 b) a @ code_to_bits (c % pow2 b) b)
