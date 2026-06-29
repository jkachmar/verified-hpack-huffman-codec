#!/usr/bin/env python3
"""Generate Hpack.Huffman.Lowstar.DfaTables.fst — the HPACK Huffman nibble DFA.

Source of truth: the F* spec table `Hpack.Huffman.Table.hpack_table` (RFC 7541
Appendix B). We enumerate, by breadth-first search from the start state (0, 0),
every partial-codeword `(acc, nbits)` reachable at a 4-bit (nibble) boundary while
decoding — exactly the states of the nibble automaton in `Hpack.Huffman.Spec.Dfa`
— and build the transition table.

`Hpack.Huffman.Refine.DfaTable` proves every emitted cell equals the spec `step`
and every accept flag equals the spec acceptance, so the generator is NOT trusted
to get them right: a slip fails `make verify`.

The 4096-cell table is emitted in CHUNK-sized pieces, not one buffer: F*'s
`igcmalloc_of_list` contents VC is O(size^2), so a single 4096-entry buffer times
out, while 256-entry buffers (the codec's existing table size) verify in ~2 s
each. The pieces sit in a buffer-of-buffers; cell `p` is at chunk `p / CHUNK`,
offset `p % CHUNK`.

Regenerate (from the fstar/ directory): make tables
"""
import re
import sys
from collections import deque

SPEC = "Hpack.Huffman.Table.fst"
EOS = 256

entries = re.findall(r"mk\s+(\d+)\s+(\d+)\s*;", open(SPEC).read())
if len(entries) != 257:
    sys.exit(f"expected 257 entries in {SPEC}, got {len(entries)}")
table = [(int(c), int(l)) for c, l in entries]      # index = symbol
bylen = {(ln, code): sym for sym, (code, ln) in enumerate(table)}


def bit_step(state, bit):
    """One MSB-first bit. Returns (next_state, emitted_sym): state is (acc, nbits)
    or None for fail; emitted_sym is a byte or None. Mirrors Spec.Dfa.bit_step."""
    if state is None:
        return None, None
    acc, nbits = state
    acc2, nb2 = acc * 2 + bit, nbits + 1
    sym = bylen.get((nb2, acc2))
    if sym is not None:
        return (None, None) if sym == EOS else ((0, 0), sym)
    return (acc2, nb2), None


def step(state, nib):
    """Advance by one nibble (four MSB-first bits); returns (state, emitted)."""
    s, emitted = state, []
    for i in (3, 2, 1, 0):
        s, sym = bit_step(s, (nib >> i) & 1)
        if sym is not None:
            emitted.append(sym)
        if s is None:
            break
    return s, emitted


# BFS from the start state, recording discovery (= id) order.
start = (0, 0)
seen, order, q = {start}, [start], deque([start])
while q:
    st = q.popleft()
    for nib in range(16):
        ns, _ = step(st, nib)
        if ns is not None and ns not in seen:
            seen.add(ns)
            order.append(ns)
            q.append(ns)

n = len(order)
maxnb = max(nb for _, nb in order)
assert maxnb < 32, f"nbits {maxnb} does not fit the *32 packing"
# Pack each state (acc, nbits) into one nat key = acc*32 + nbits (nbits < 32), so
# the F* proof scans a `list nat` (nat compares) rather than a `list (nat&nat)`.
keys = [a * 32 + nb for a, nb in order]
sid = {st: i for i, st in enumerate(order)}

# Flat transition table, row-major (state*16 + nibble). Each cell packs the
# transition into one u32: next_id*65536 + emit_flag*256 + sym (next_id in [0, n];
# the fail id n means "reject"). The accept array marks padding-valid states.
cells, accept = [], []
for i, (a, m) in enumerate(order):
    accept.append(1 if (m <= 7 and a == (1 << m) - 1) else 0)
    for nib in range(16):
        ns, emitted = step((a, m), nib)
        assert len(emitted) <= 1, f"nibble emitted {len(emitted)} bytes"
        nid = n if ns is None else sid[ns]
        flag, sym = (1, emitted[0]) if emitted else (0, 0)
        cells.append(nid * 65536 + flag * 256 + sym)

NC = len(cells)
assert NC == n * 16 and all(c < (1 << 32) for c in cells)

CHUNK = 256
assert NC % CHUNK == 0, f"{NC} cells not divisible by chunk size {CHUNK}"
NCH = NC // CHUNK
chunks = [cells[k * CHUNK:(k + 1) * CHUNK] for k in range(NCH)]

keystr = ";\n    ".join(f"{k}" for k in keys)
acceptstr = ";\n    ".join(f"{v}uy" for v in accept)


def chunk_list_def(k):
    body = ";\n    ".join(f"{c}ul" for c in chunks[k])
    # Two bindings, no duplicated data:
    #   * `_data` is a BARE `inline_for_extraction` list literal. KaRaMeL lowers
    #     `igcmalloc_of_list` to `createL`, which needs a *syntactic* list literal at
    #     the call site; inlining a bare-literal binding yields exactly that (a
    #     `noextract` binding, or one wrapped in `let ... in assert_norm; l`, does
    #     not — hence the dedicated `_data`).
    #   * `_list` is the length-refined proof/recall binding, DEFINED FROM `_data`,
    #     so `seq_of_list _list` reduces to `seq_of_list _data` in one delta step
    #     (the buffer's contents match stays cheap — no element-wise/superlinear VC).
    return (f"inline_for_extraction let dfa_chunk_{k}_data : list U32.t = [\n    {body}\n  ]\n"
            f"noextract let dfa_chunk_{k}_list : (l:list U32.t{{ L.length l == dfa_chunk_size }}) =\n"
            f"  assert_norm (L.length dfa_chunk_{k}_data == dfa_chunk_size);\n  dfa_chunk_{k}_data")


def chunk_buf_def(k):
    # Build from `_data` (the bare literal → `createL`); annotate the witnessed
    # contents with `_list` (what the proof/`read_at` recall against). The two are
    # defeq, so the type-check is a single unfold.
    return (f"let dfa_chunk_{k}\n"
            f"  : b:IB.libuffer U32.t (normalize_term (L.length dfa_chunk_{k}_data)) "
            f"(Seq.seq_of_list dfa_chunk_{k}_list){{ IB.recallable b }} =\n"
            f"  IB.igcmalloc_of_list HS.root dfa_chunk_{k}_data")


chunk_lists = "\n\n".join(chunk_list_def(k) for k in range(NCH))
chunk_bufs = "\n\n".join(chunk_buf_def(k) for k in range(NCH))
outer_elems = "; ".join(f"dfa_chunk_{k}" for k in range(NCH))

# This module emits only DATA + mechanical buffer declarations. The proof glue
# that ranges over the chunks (the `dfa_chunk_list` selector and the `outer_chunk`
# recall helper) is hand-written in `Hpack.Huffman.Refine.DfaTable`, so all proof
# reasoning is human-authored and reviewed — the generator is never trusted to
# emit a proof, only data that F* checks against the spec.

print(f'''module Hpack.Huffman.Lowstar.DfaTables

/// GENERATED FILE — do not edit by hand.
/// Regenerate: `make tables` (from the fstar/ directory).
///
/// The HPACK Huffman nibble DFA, enumerated by BFS from the start state (0, 0)
/// over the spec table `Hpack.Huffman.Table.hpack_table`. State ids are the BFS
/// (discovery) order; the fail state is the out-of-range id {n}.
///
///   * `dfa_state_keys` — each reachable state `(acc, nbits)` packed as
///     `acc*32 + nbits` (nbits < 32); proof-only (`noextract`). Maps ids -> states.
///   * `dfa_chunk_k` / `dfa_chunks` — the executable transition table, split into
///     {NCH} pieces of {CHUNK} cells (row-major `state*16 + nibble`) held in a
///     buffer-of-buffers; cell `p` is `dfa_chunks[p / {CHUNK}][p % {CHUNK}]`, a u32
///     `next_id*65536 + emit_flag*256 + sym`. (One 4096-entry buffer is O(n^2) to
///     verify and times out; {CHUNK}-entry pieces verify fast.)
///   * `dfa_accept` — per state, 1 iff stopping there is valid padding.
///
/// `Hpack.Huffman.Refine.DfaTable` proves every chunk cell equals the spec step and
/// every accept flag the spec acceptance, so the generator is not trusted: a slip
/// fails `make verify`.

open FStar.HyperStack.ST
module IB = LowStar.ImmutableBuffer
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module HS = FStar.HyperStack
module Seq = FStar.Seq
module L = FStar.List.Tot

/// Number of reachable states; the fail state is the out-of-range id.
noextract let dfa_n_states : nat = {n}

/// Cells per chunk, number of chunks, total cells (`dfa_n_states * 16`).
noextract let dfa_chunk_size : nat = {CHUNK}
noextract let dfa_n_chunks : nat = {NCH}
noextract let dfa_n_cells : nat = {NC}

/// The {n} reachable states' packed keys, in BFS (id) order. The refined length
/// lets `state_of` index without an inline `assert_norm` (a normaliser footgun).
noextract let dfa_state_keys : (l:list nat{{ L.length l == dfa_n_states }}) =
  let l : list nat = [
    {keystr}
  ] in
  assert_norm (L.length l == dfa_n_states);
  l

(* Transition-table chunks (each {CHUNK} cells of the row-major flat table). *)

{chunk_lists}

(* Executable chunk buffers (natural `igcmalloc_of_list` return type — see the
   header: the opaque-contents match VC is superlinear at large sizes). The chunks
   are read by `Hpack.Huffman.Lowstar.Dfa.read_cell`, a 16-way `match` over these
   named buffers (a C `switch`); the `dfa_chunk_list` selector used by the proof is
   hand-written in `Hpack.Huffman.Refine.DfaTable`. *)

{chunk_bufs}

/// Per-state accept flag: 1 iff the state is a valid stopping point (padding).
/// 256 entries — one buffer is in the fast regime, no chunking needed. Refined
/// length so the proof can index it generically (cf. `dfa_state_keys`).
inline_for_extraction let dfa_accept_data : list U8.t = [
    {acceptstr}
  ]
noextract let dfa_accept_list : (l:list U8.t{{ L.length l == dfa_n_states }}) =
  assert_norm (L.length dfa_accept_data == dfa_n_states);
  dfa_accept_data
noextract let dfa_accept_contents : Seq.seq U8.t = Seq.seq_of_list dfa_accept_list
let dfa_accept
  : b:IB.libuffer U8.t (normalize_term (L.length dfa_accept_data)) dfa_accept_contents{{ IB.recallable b }} =
  IB.igcmalloc_of_list HS.root dfa_accept_data
''')
