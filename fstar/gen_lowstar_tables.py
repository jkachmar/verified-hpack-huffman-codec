#!/usr/bin/env python3
"""Generate Hpack.Huffman.Lowstar.Tables.fst — the *executable* HPACK Huffman
tables as Low* immutable global buffers (KaRaMeL lowers each to a C array).

Source of truth: the F* spec table `Hpack.Huffman.Table.hpack_table` (RFC 7541
Appendix B), whose RFC invariants (lengths in [5,30], distinctness,
prefix-freeness, EOS code) are proved in `Hpack.Huffman.Table.Properties`.
Deriving the executable tables from the proven spec keeps them provably
consistent with it.

The list literals are emitted inline at the `igcmalloc_of_list` call site so
KaRaMeL's of-list -> const-array pass fires (a named binding would instead
compile to a runtime-built linked list). 256 entries: bytes 0..255 only; the
EOS symbol (256) is never produced by the encoder and never a decode match.

The two sorted decode tables additionally get named `noextract` lists
(`sorted_key_list` / `sorted_sym_list`) backing their `_contents` sequences.
Proofs walk those *lists* with `assert_norm` (`Seq.index` does not reduce through
`Seq.seq_of_list`, but list indexing does) and transport the per-index facts onto
the sequences via `FStar.Seq` lemmas. The lists are `noextract`, so they add
nothing to the generated C.

Two table families:
  * Encoder, indexed by byte:  huff_code[b], huff_len[b].
  * Decoder, sorted by (len, code) so the per-bit lookup is a binary search:
    sorted_key[i] = len*2^30 + code (strictly increasing; codes are < 2^30),
    sorted_sym[i] = the byte whose code that is.

Regenerate (from the fstar/ directory): make tables
"""
import re, sys

spec = open("Hpack.Huffman.Table.fst").read()
entries = re.findall(r"mk\s+(\d+)\s+(\d+)\s*;", spec)
if len(entries) != 257:
    sys.exit(f"expected 257 entries in Hpack.Huffman.Table.fst, got {len(entries)}")

# Bytes 0..255 (drop EOS = index 256). (code, len) per byte.
table = [(int(c), int(l)) for c, l in entries[:256]]
for b, (code, ln) in enumerate(table):
    if not (5 <= ln <= 30):
        sys.exit(f"byte {b}: length {ln} outside RFC [5,30]")
    if code >= (1 << 30):
        sys.exit(f"byte {b}: code {code} does not fit in 30 bits")

codes = ";\n    ".join(f"{code}ul" for code, _ in table)
lens  = ";\n    ".join(f"{ln}uy"   for _, ln in table)

print(f'''module Hpack.Huffman.Lowstar.Tables

/// GENERATED FILE — do not edit by hand.
/// Regenerate: `make tables` (from the fstar/ directory).
///
/// Executable HPACK Huffman tables (RFC 7541 Appendix B), as Low* immutable
/// global buffers; KaRaMeL lowers each to a C array.
///
/// Derived from `Hpack.Huffman.Table.hpack_table`, whose RFC invariants are proved
/// in `Hpack.Huffman.Table.Properties` (lengths, distinctness, prefix-freeness).
/// `Hpack.Huffman.Refine.Encode` proves the per-byte encode tables here equal the
/// spec's `code_of`/`len_of` — so the values are under proof, not assumed. (The
/// decoder is the verified nibble DFA in `Hpack.Huffman.Lowstar.Dfa`, with its own
/// generated table; this module is now encode-only.)

open FStar.HyperStack.ST
module IB = LowStar.ImmutableBuffer
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module HS = FStar.HyperStack
module Seq = FStar.Seq

/// Encoder table, indexed by byte: right-aligned code bit-pattern. Contents are
/// witnessed in the type (`libuffer ... huff_code_contents`, backed by the named
/// `huff_code_list`) so `Hpack.Huffman.Refine.Encode` can `recall_contents` and
/// prove each byte's code equals the spec's `code_of` (the opaque-contents idiom).
noextract let huff_code_list : list U32.t = [
    {codes}
  ]
[@@ "opaque_to_smt"]
noextract let huff_code_contents : (s:Seq.seq U32.t{{ Seq.length s == 256 }}) =
  assert_norm (FStar.List.Tot.length huff_code_list == 256);
  Seq.seq_of_list huff_code_list
let huff_code : b:IB.libuffer U32.t 256 huff_code_contents{{ IB.length b == 256 /\\ IB.recallable b }} =
  reveal_opaque (`%huff_code_contents) huff_code_contents;
  IB.igcmalloc_of_list HS.root [
    {codes}
  ]

/// Encoder table, indexed by byte: code bit-length. The element type carries the
/// RFC's [5, 30] bound intrinsically, so every read is in range; contents are
/// witnessed (backed by `huff_len_list`) for the `Refine.Encode` proof that each
/// byte's length equals the spec's `len_of`.
noextract let huff_len_list : list (x:U8.t{{ 5 <= U8.v x /\\ U8.v x <= 30 }}) = [
    {lens}
  ]
[@@ "opaque_to_smt"]
noextract let huff_len_contents
  : (s:Seq.seq (x:U8.t{{ 5 <= U8.v x /\\ U8.v x <= 30 }}){{ Seq.length s == 256 }}) =
  assert_norm (FStar.List.Tot.length huff_len_list == 256);
  Seq.seq_of_list huff_len_list
let huff_len
  : b:IB.libuffer (x:U8.t{{ 5 <= U8.v x /\\ U8.v x <= 30 }}) 256 huff_len_contents{{ IB.length b == 256 /\\ IB.recallable b }} =
  reveal_opaque (`%huff_len_contents) huff_len_contents;
  IB.igcmalloc_of_list HS.root [
    {lens}
  ]
''')
