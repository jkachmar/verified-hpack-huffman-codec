module Hpack.Huffman.Bridge.Decode

/// Pure bridge lemmas for the imperative ⇄ spec decode simulation
/// (`Hpack.Huffman.Lowstar.Dfa.dfa_loop` ⇄ `Spec.Codec.decode_go`), RFC-agnostic
/// and heap-free so they verify fast and keep the intrinsic loop proof small:
///
///   * `decoded_prefix` and its update lemmas — the decoded-byte *prefix* of a
///     `dst` buffer as a spec `list byte`, and how an in-bounds `upd` at the write
///     cursor snocs one byte onto it (mirroring `decode_go`'s `out @ [b]`);
///   * `decode_go_grows` / `decode_go_nil` — `decode_go` only appends to its
///     output, and its end-of-input verdict is `valid_padding_v`; together they
///     discharge the loop's `dst`-overflow and end-of-stream branches.

open Hpack.Huffman.Spec.Codec
open FStar.Mul
module L = FStar.List.Tot
module Seq = FStar.Seq
module U8 = FStar.UInt8

#set-options "--fuel 2 --ifuel 1 --z3rlimit 40"

(* ---------------------------------------------------------------------- *)
(* dst prefix as a spec byte list                                          *)
(* ---------------------------------------------------------------------- *)

(* `byte_of` and `decoded_prefix` are the transparent definitions exposed in the
   interface (Hpack.Huffman.Bridge.Decode.fsti) — visible here. *)

/// `L.length (l @ [x]) == L.length l + 1` as a single fact (so a `--fuel 0`
/// consumer need not unfold `L.length [x]`).
let len_snoc (#a:Type) (l:list a) (x:a) : Lemma (L.length (l @ [x]) == L.length l + 1)
  = L.append_length l [x]

let rec decoded_prefix_length (s:Seq.seq U8.t) (n:nat{n <= Seq.length s})
  : Lemma (ensures L.length (decoded_prefix s n) == n) (decreases n)
  = if n = 0 then ()
    else (decoded_prefix_length s (n - 1);
          L.append_length (decoded_prefix s (n - 1)) [byte_of (Seq.index s (n - 1))])

/// Updating `s` at index `i >= n` leaves its first-`n` prefix list unchanged.
let rec decoded_prefix_upd (s:Seq.seq U8.t) (i:nat) (v:U8.t) (n:nat{n <= i /\ i < Seq.length s})
  : Lemma (ensures decoded_prefix (Seq.upd s i v) n == decoded_prefix s n) (decreases n)
  = if n = 0 then ()
    else (decoded_prefix_upd s i v (n - 1);
          Seq.lemma_index_upd2 s i v (n - 1))   // (upd s i v)[n-1] == s[n-1] since n-1 < i

/// Writing `v` at the cursor `n` snocs `byte_of v` onto the first-`n` prefix list.
let decoded_prefix_upd_snoc (s:Seq.seq U8.t) (n:nat{n < Seq.length s}) (v:U8.t)
  : Lemma (decoded_prefix (Seq.upd s n v) (n + 1) == decoded_prefix s n @ [byte_of v])
  = decoded_prefix_upd s n v n;                  // decoded_prefix (upd s n v) n == decoded_prefix s n
    Seq.lemma_index_upd1 s n v          // (upd s n v)[n] == v

/// `decode_go` only ever appends to its output accumulator, so when it accepts,
/// the decoded list is at least as long as the seed. The simulation uses this to
/// show the loop's `dst`-overflow `-1` branch is unreachable on accepted streams:
/// an emit that would overflow `dst_cap` makes the final length exceed `dst_cap`.
let rec decode_go_grows (input:list bool) (acc nbits:nat) (out:list byte)
  : Lemma (ensures (Some? (decode_go input acc nbits out) ==>
                    L.length (Some?.v (decode_go input acc nbits out)) >= L.length out))
          (decreases (L.length input))
  = match input with
    | [] -> ()
    | b :: rest ->
        let acc' = acc * 2 + (if b then 1 else 0) in
        (match lookup_v acc' (nbits + 1) with
         | Some s -> if s = eos_index then ()
                     else (decode_go_grows rest 0 0 (out @ [s]);
                           L.append_length out [s])
         | None -> decode_go_grows rest acc' (nbits + 1) out)

/// End-of-input behaviour of `decode_go` (definitional; lets the decoder's base
/// case avoid unfolding `decode_go` when run at `--fuel 0`).
let decode_go_nil (acc nbits:nat) (out:list byte)
  : Lemma (decode_go [] acc nbits out == (if valid_padding_v acc nbits then Some out else None)) = ()
