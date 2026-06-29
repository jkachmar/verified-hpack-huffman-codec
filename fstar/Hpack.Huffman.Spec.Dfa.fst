module Hpack.Huffman.Spec.Dfa

/// The HPACK Huffman decoder modelled as a nibble-driven automaton — the pure
/// spec the verified table-driven decoder will refine (see `ARCHITECTURE.md`,
/// *Future design goals*). This module defines only the model and its sanity
/// facts; the equivalence to the greedy `Spec.Codec.decode_go` lives in
/// `Hpack.Huffman.Spec.DfaEquiv`, and the executable finite table in
/// `Hpack.Huffman.Lowstar.Dfa`.
///
/// Design choice (the deferred D1 decision): the automaton's state *is* the
/// `(acc, nbits)` partial-codeword the greedy decoder carries — `DLive acc nbits`
/// — plus an absorbing `DFail` for an in-stream EOS. So the abstraction relation
/// to `decode_go` is essentially the identity, and a single-bit transition
/// (`bit_step`) is `decode_go`'s per-bit step verbatim. The model is therefore
/// *not* finite-state (the no-match branch grows `nbits` without bound); turning
/// it into a finite, indexable table — collapsing the unreachable `nbits > 30`
/// tail to a fail state — is the job of the executable layer (D3), justified by
/// `Refine.Decode.decode_go_overlong`.

open Hpack.Huffman.Spec.Codec
open FStar.Mul
open FStar.List.Tot
module L = FStar.List.Tot

#set-options "--fuel 1 --ifuel 1 --z3rlimit 20"

(* ---------------------------------------------------------------------- *)
(* States and the single-bit transition                                    *)
(* ---------------------------------------------------------------------- *)

/// An automaton state: either the in-flight partial codeword `(acc, nbits)`
/// (`acc` is the `nbits`-bit value accumulated since the last emit), or the
/// absorbing failure reached on an in-stream EOS match.
noextract type dstate =
  | DFail : dstate
  | DLive : acc:nat -> nbits:nat -> dstate

/// The start state: empty accumulator (also an accepting state — the empty input
/// is valid).
noextract let dfa_init : dstate = DLive 0 0

/// One bit of input, MSB-first. This is exactly the body of `decode_go`'s
/// `b :: rest` case lifted to an explicit state: extend the accumulator, and on a
/// codeword match emit the byte and reset (an EOS match is the only failure).
noextract let bit_step (s:dstate) (b:bool) : dstate & option byte =
  match s with
  | DFail -> DFail, None
  | DLive acc nbits ->
      let acc' = acc * 2 + (if b then 1 else 0) in
      let nbits' = nbits + 1 in
      (match lookup_v acc' nbits' with
       | Some sy -> if sy = eos_index then DFail, None
                    else DLive 0 0, Some sy
       | None -> DLive acc' nbits', None)

/// Run a bit string through the automaton, collecting emitted bytes in order.
/// The shared primitive behind both `step` (per nibble) and the `decode_go`
/// bridge in `Refine.Dfa`.
noextract let rec bits_step (s:dstate) (bs:list bool)
  : Tot (dstate & list byte) (decreases bs) =
  match bs with
  | [] -> s, []
  | b :: tl ->
      let s1, o1 = bit_step s b in
      let s2, o2 = bits_step s1 tl in
      s2, (match o1 with None -> [] | Some ob -> [ob]) @ o2

(* ---------------------------------------------------------------------- *)
(* The nibble transition and the run                                       *)
(* ---------------------------------------------------------------------- *)

/// A 4-bit input chunk.
noextract let nibble = n:nat{n < 16}

/// The four bits of a nibble, MSB-first (bit of value 8 down to value 1) — the
/// order in which `Spec.Decode.bytes_to_bits` yields them within a byte.
noextract let nibble_bits (n:nibble) : list bool =
  [ (n / 8) % 2 = 1; (n / 4) % 2 = 1; (n / 2) % 2 = 1; n % 2 = 1 ]

/// The transition the executable table implements: advance the state by one
/// nibble, emitting 0, 1, or 2 bytes.
noextract let step (s:dstate) (n:nibble) : dstate & list byte =
  bits_step s (nibble_bits n)

/// Run a nibble sequence from a state, collecting emitted bytes in order.
noextract let rec dfa_run (s:dstate) (ns:list nibble)
  : Tot (dstate & list byte) (decreases ns) =
  match ns with
  | [] -> s, []
  | n :: tl ->
      let s1, o1 = step s n in
      let s2, o2 = dfa_run s1 tl in
      s2, o1 @ o2

(* ---------------------------------------------------------------------- *)
(* State classification and acceptance                                     *)
(* ---------------------------------------------------------------------- *)

/// The absorbing failure state (in-stream EOS).
noextract let is_fail (s:dstate) : bool = DFail? s

/// A state where it is valid to stop: the residual partial codeword is at most
/// 7 all-ones padding bits (the executable table records this as a per-state
/// `accepting` flag).
noextract let is_accepting (s:dstate) : bool =
  match s with
  | DFail -> false
  | DLive acc nbits -> valid_padding_v acc nbits

/// Decode a whole nibble sequence: run it, then accept iff it neither failed nor
/// stopped mid-codeword — exactly `decode_go`'s end-of-input rule.
noextract let dfa_decode (ns:list nibble) : option (list byte) =
  let s, out = dfa_run dfa_init ns in
  if is_accepting s then Some out else None

(* ---------------------------------------------------------------------- *)
(* Sanity                                                                   *)
(* ---------------------------------------------------------------------- *)

/// The start state accepts (empty padding is valid).
noextract let dfa_init_accepting (_:unit) : Lemma (is_accepting dfa_init)
  = assert_norm (pow2 0 == 1)

/// Empty input decodes to the empty byte string.
noextract let dfa_decode_nil (_:unit) : Lemma (dfa_decode [] == Some [])
  = assert_norm (pow2 0 == 1)

/// `step` is, by definition, four single-bit steps over the nibble's bits — the
/// hook the `decode_go` bridge (D2) unfolds.
noextract let step_unfold (s:dstate) (n:nibble)
  : Lemma (step s n == bits_step s (nibble_bits n)) = ()
