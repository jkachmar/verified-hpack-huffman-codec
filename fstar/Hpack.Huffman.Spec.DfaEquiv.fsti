module Hpack.Huffman.Spec.DfaEquiv

/// Interface: the nibble automaton (`Spec.Dfa`) decodes exactly what the greedy
/// spec (`Spec.Codec.decode_go`) does.
///
/// Exposed: the headline equivalence `dfa_decode_correct` (automaton run ==
/// `decode_bits` of the flattened bits) — the module's reason for being — and the
/// per-step `decode_go_nibble` the imperative loop (`Lowstar.Dfa`) actually runs
/// on, plus the transparent `nibbles_to_bits` their statements mention. Sealed in
/// the `.fst`: the inductive scaffolding (`DFail`-absorbing, the bit-granular
/// `bits_step == decode_go`, the concatenation homomorphism, the nibble fold).

open Hpack.Huffman.Spec.Codec
open Hpack.Huffman.Spec.Dfa
open FStar.Mul
open FStar.List.Tot
module L = FStar.List.Tot

/// A nibble sequence as its flattened MSB-first bit string.
let rec nibbles_to_bits (ns:list nibble) : list bool =
  match ns with
  | [] -> []
  | n :: tl -> nibble_bits n @ nibbles_to_bits tl

/// THE EQUIVALENCE: running the automaton over a nibble sequence yields exactly
/// `decode_bits` of that sequence's flattened MSB-first bits.
val dfa_decode_correct (ns:list nibble)
  : Lemma (dfa_decode ns == decode_bits (nibbles_to_bits ns))

/// One automaton step == stepping `decode_go` by that step's bits: feeding
/// `bits_step` the prefix `four` either fails (in-stream EOS — `decode_go` rejects
/// the whole stream) or lands in `DLive a n` emitting `o1`, in which case decoding
/// `four @ rest` from `(acc, nbits)` is decoding `rest` from `(a, n)` with `o1`
/// appended. (The loop instantiates `four` with a nibble's four bits.)
val decode_go_nibble (four rest:list bool) (acc nbits:nat) (out:list byte)
  : Lemma
      (let s1, o1 = bits_step (DLive acc nbits) four in
       decode_go (four @ rest) acc nbits out ==
       (match s1 with
        | DFail -> None
        | DLive a n -> decode_go rest a n (out @ o1)))
