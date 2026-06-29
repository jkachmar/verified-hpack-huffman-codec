module Hpack.Huffman.Spec.DfaEquiv

/// The nibble automaton (`Spec.Dfa`) decodes exactly what the greedy spec
/// (`Spec.Codec.decode_go`) does. This is the heart of the DFA rewrite: it
/// licenses replacing the per-bit decoder with a table-driven one while keeping
/// `decode_go` as the single source of decode truth.
///
/// The chain:
///   * `bits_step_decode_go` — running the automaton bit-by-bit equals
///     `decode_go`, with the collected output gated on the final state being
///     accepting (the σ relation is the identity: a `DLive acc nbits` state *is*
///     `decode_go`'s `(acc, nbits)`);
///   * `bits_step_append` — `bits_step` is a monoid homomorphism over bit-string
///     concatenation, so a run splits at any boundary;
///   * `dfa_run_bits` / `dfa_decode_correct` — folding by nibbles equals folding
///     the flattened bit string, giving `dfa_decode ns == decode_bits
///     (nibbles_to_bits ns)`.
///
/// The remaining step — that a byte buffer's MSB-first bit view equals the
/// flattened bits of its nibbles — lives with the imperative decoder
/// (`Lowstar.Dfa`), alongside the analogous encode-side view bridge.

open Hpack.Huffman.Spec.Codec
open Hpack.Huffman.Spec.Dfa
open FStar.Mul
open FStar.List.Tot
module L = FStar.List.Tot

#set-options "--fuel 2 --ifuel 1 --z3rlimit 30"

(* ---------------------------------------------------------------------- *)
(* DFail is absorbing                                                      *)
(* ---------------------------------------------------------------------- *)

/// Once failed, the automaton stays failed and emits nothing.
let rec bits_step_fail (bs:list bool)
  : Lemma (ensures bits_step DFail bs == (DFail, [])) (decreases bs)
  = match bs with
    | [] -> ()
    | _ :: tl -> bits_step_fail tl

(* ---------------------------------------------------------------------- *)
(* The automaton equals decode_go (bit-granular)                           *)
(* ---------------------------------------------------------------------- *)

/// Running `bits_step` from `DLive acc nbits` over `bs` reproduces
/// `decode_go bs acc nbits out`: the residual state's acceptance is exactly
/// `decode_go`'s end-of-input verdict, and the bytes it collects are exactly the
/// ones `decode_go` would append to `out`.
let rec bits_step_decode_go (bs:list bool) (acc nbits:nat) (out:list byte)
  : Lemma
      (ensures
        decode_go bs acc nbits out ==
        (let s', em = bits_step (DLive acc nbits) bs in
         match s' with
         | DFail -> None
         | DLive a n -> if valid_padding_v a n then Some (out @ em) else None))
      (decreases bs)
  = match bs with
    | [] -> L.append_l_nil out                 // out @ [] == out
    | b :: rest ->
        let acc' = acc * 2 + (if b then 1 else 0) in
        (match lookup_v acc' (nbits + 1) with
         | Some s ->
             if s = eos_index then
               bits_step_fail rest             // both sides None
             else begin
               bits_step_decode_go rest 0 0 (out @ [s]);
               let _, o2 = bits_step (DLive 0 0) rest in
               L.append_assoc out [s] o2        // (out @ [s]) @ o2 == out @ ([s] @ o2)
             end
         | None ->
             bits_step_decode_go rest acc' (nbits + 1) out)

(* ---------------------------------------------------------------------- *)
(* bits_step is a homomorphism over concatenation                          *)
(* ---------------------------------------------------------------------- *)

let rec bits_step_append (s:dstate) (xs ys:list bool)
  : Lemma
      (ensures
        bits_step s (xs @ ys) ==
        (let s1, o1 = bits_step s xs in
         let s2, o2 = bits_step s1 ys in
         (s2, o1 @ o2)))
      (decreases xs)
  = match xs with
    | [] -> ()
    | x :: tl ->
        let s1, p1 = bit_step s x in
        bits_step_append s1 tl ys;
        let c1, c2 = bits_step s1 tl in
        let _, o2 = bits_step c1 ys in
        L.append_assoc (match p1 with None -> [] | Some ob -> [ob]) c2 o2

(* ---------------------------------------------------------------------- *)
(* Folding nibbles equals folding the flattened bits                       *)
(* ---------------------------------------------------------------------- *)

(* `nibbles_to_bits` is the transparent definition exposed in the interface. *)

let rec dfa_run_bits (s:dstate) (ns:list nibble)
  : Lemma (ensures dfa_run s ns == bits_step s (nibbles_to_bits ns))
          (decreases ns)
  = match ns with
    | [] -> ()
    | n :: tl ->
        let s1, _ = step s n in
        bits_step_append s (nibble_bits n) (nibbles_to_bits tl);
        dfa_run_bits s1 tl

(* ---------------------------------------------------------------------- *)
(* Top-level: the automaton decodes exactly decode_bits                    *)
(* ---------------------------------------------------------------------- *)

let dfa_decode_correct (ns:list nibble)
  : Lemma (dfa_decode ns == decode_bits (nibbles_to_bits ns))
  = dfa_run_bits dfa_init ns;
    bits_step_decode_go (nibbles_to_bits ns) 0 0 [];
    let _, out = dfa_run dfa_init ns in
    L.append_nil_l out                          // [] @ out == out

(* ---------------------------------------------------------------------- *)
(* One automaton step = stepping decode_go by that step's bits             *)
(* ---------------------------------------------------------------------- *)

/// The inductive step the imperative nibble loop needs: feeding `bits_step` the
/// prefix `four` either fails (an in-stream EOS — `decode_go` rejects the whole
/// stream) or lands in `DLive a n` emitting `o1`, in which case decoding
/// `four @ rest` from `(acc, nbits)` is decoding `rest` from `(a, n)` with `o1`
/// appended to the output. (`four` is any prefix; the loop instantiates it with a
/// nibble's four bits.)
let decode_go_nibble (four rest:list bool) (acc nbits:nat) (out:list byte)
  : Lemma
      (let s1, o1 = bits_step (DLive acc nbits) four in
       decode_go (four @ rest) acc nbits out ==
       (match s1 with
        | DFail -> None
        | DLive a n -> decode_go rest a n (out @ o1)))
  = bits_step_append (DLive acc nbits) four rest;
    bits_step_decode_go (four @ rest) acc nbits out;
    let s1, o1 = bits_step (DLive acc nbits) four in
    match s1 with
    | DFail -> bits_step_fail rest
    | DLive a n ->
        bits_step_decode_go rest a n (out @ o1);
        let _, o2 = bits_step s1 rest in
        L.append_assoc out o1 o2
