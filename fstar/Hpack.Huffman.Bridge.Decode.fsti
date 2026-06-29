module Hpack.Huffman.Bridge.Decode

/// Interface for the imperative ⇄ spec decode bridge.
///
/// Exposed: the transparent `decoded_prefix` (a `dst` buffer's decoded-byte prefix
/// as a spec `list byte`, snoc-built to mirror `decode_go`'s `out @ [b]`) and the
/// facts the loop needs about it (`_length`, `_upd_snoc`, `len_snoc`), plus the two
/// `decode_go` end-conditions the loop reasons with (`decode_go_nil`,
/// `decode_go_grows`). Sealed in the `.fst`: the `> 30`-bit rejection lemmas
/// (`decode_go_overlong`, `lookup_none_overlong*`) and `decode_go_cons` — bridge
/// helpers for the retired per-bit loop, kept here only as spec facts.

open Hpack.Huffman.Spec.Codec
open FStar.Mul
module L = FStar.List.Tot
module Seq = FStar.Seq
module U8 = FStar.UInt8

let byte_of (x:U8.t) : byte = U8.v x

/// `L.length (l @ [x]) == L.length l + 1` as a single fact (so a `--fuel 0`
/// consumer need not unfold `L.length [x]`).
val len_snoc (#a:Type) (l:list a) (x:a) : Lemma (L.length (l @ [x]) == L.length l + 1)

/// The first `n` bytes of `s`, as a spec byte list (snoc-built, matching the way
/// `decode_go` grows its output by `out @ [b]`).
let rec decoded_prefix (s:Seq.seq U8.t) (n:nat{n <= Seq.length s}) : Tot (list byte) (decreases n) =
  if n = 0 then [] else decoded_prefix s (n - 1) @ [byte_of (Seq.index s (n - 1))]

val decoded_prefix_length (s:Seq.seq U8.t) (n:nat{n <= Seq.length s})
  : Lemma (L.length (decoded_prefix s n) == n)

/// Writing `v` at the cursor `n` snocs `byte_of v` onto the first-`n` prefix list.
val decoded_prefix_upd_snoc (s:Seq.seq U8.t) (n:nat{n < Seq.length s}) (v:U8.t)
  : Lemma (decoded_prefix (Seq.upd s n v) (n + 1) == decoded_prefix s n @ [byte_of v])

/// `decode_go` only ever appends to its output, so on acceptance the decoded list
/// is at least as long as the seed (the loop uses this to show its `dst`-overflow
/// `-1` branch is unreachable on accepted streams).
val decode_go_grows (input:list bool) (acc nbits:nat) (out:list byte)
  : Lemma (Some? (decode_go input acc nbits out) ==>
           L.length (Some?.v (decode_go input acc nbits out)) >= L.length out)

/// End-of-input behaviour of `decode_go` (definitional; lets the decoder's base
/// case avoid unfolding `decode_go` at `--fuel 0`).
val decode_go_nil (acc nbits:nat) (out:list byte)
  : Lemma (decode_go [] acc nbits out == (if valid_padding_v acc nbits then Some out else None))
