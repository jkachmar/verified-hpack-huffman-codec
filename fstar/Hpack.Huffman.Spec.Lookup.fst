module Hpack.Huffman.Spec.Lookup

/// Codeword-lookup correctness, derived from the table's pairwise
/// prefix-freeness. These are the facts the round-trip proof leans on:
///   * `no_match_general` — a *different* symbol is never the length-`k` prefix
///     value of `b`'s code (else its code would prefix `b`'s);
///   * `lookup_correct`   — looking up `b`'s own (code, length) returns `b`;
///   * `no_proper_prefix` — looking up any proper prefix of `b`'s code (a shorter
///     length) returns nothing.

open Hpack.Huffman.Table
open Hpack.Huffman.Spec.Codec
open FStar.Mul
module L = FStar.List.Tot
module P = Hpack.Huffman.Table.Properties

#set-options "--fuel 1 --ifuel 1 --z3rlimit 40"

/// Core: a *different* symbol cannot be the length-k prefix value of `b`'s code.
/// If it were (`len_of i == k` and `code_of i == top-k-bits of code_of b`), then
/// `i`'s code is a prefix of `b`'s code, contradicting prefix-freeness. Stated for
/// any symbol `b` (including EOS), since only prefix-freeness over the 257 entries
/// is used — the padding proof reuses it at `b = eos_index`.
noextract let no_match_general (b:sym) (i:nat{i < 257}) (k:nat{k <= len_of b})
  : Lemma (requires i <> b)
          (ensures ~(len_of i == k /\ code_of i == code_of b / pow2 (len_of b - k)))
  = P.lemma_table_complete ();
    P.lemma_prefix_free ();
    if i < b then P.prefix_free_index hpack_table i b
    else (P.prefix_free_index hpack_table b i; P.no_prefix_sym (entry_at b) (entry_at i))

/// `lookup_v (code b) (len b) == Some b`: the search returns `b`. No earlier
/// symbol matches (it would duplicate `b`'s code, impossible by distinctness).
noextract let rec lookup_correct_go (b:byte) (i:nat{i <= b})
  : Lemma (ensures find_v (code_of b) (len_of b) i == Some b) (decreases (b - i))
  = if i = b then ()
    else begin
      no_match_general b i (len_of b);   // pow2 (len_of b - len_of b) = pow2 0 = 1
      lookup_correct_go b (i + 1)
    end

noextract let lookup_correct (b:byte)
  : Lemma (lookup_v (code_of b) (len_of b) == Some b)
  = lookup_correct_go b 0

/// `lookup_v (top-k-bits of code b) k == None` for any proper prefix length
/// k < len b: no symbol has that (length, value). Stated for any symbol `b`
/// (the padding proof instantiates it at `b = eos_index`).
noextract let rec no_proper_prefix_go (b:sym) (k:nat{k < len_of b}) (i:nat{i <= 257})
  : Lemma (ensures find_v (code_of b / pow2 (len_of b - k)) k i == None)
          (decreases (257 - i))
  = if i = 257 then ()
    else begin
      (if i = b then ()                         // len_of b <> k, so no match
       else no_match_general b i k);
      no_proper_prefix_go b k (i + 1)
    end

noextract let no_proper_prefix (b:sym) (k:nat{k < len_of b})
  : Lemma (lookup_v (code_of b / pow2 (len_of b - k)) k == None)
  = no_proper_prefix_go b k 0
