module Hpack.Huffman

/// Public entry points of the HPACK Huffman codec — the C ABI the
/// FFI shim links against. These are thin re-exports of the verified codec
/// (`Hpack.Huffman.Lowstar.Codec`); keeping them in this module makes it the
/// bundle's public interface, so KaRaMeL lowers the whole implementation to one
/// `Hpack_Huffman.{c,h}` with the `Hpack_Huffman_*` symbol prefix the shim calls.
///
/// Each entry restates the codec's calling preconditions (so the call type-checks)
/// and exposes the memory-effect guarantee; the full functional contract is proved
/// at the codec definitions.

open FStar.HyperStack.ST
open FStar.Mul
module B    = LowStar.Buffer
module MB   = LowStar.Monotonic.Buffer
module U8   = FStar.UInt8
module U32  = FStar.UInt32
module I32  = FStar.Int32
open Hpack.Huffman.Lowstar.Tables
module Codec = Hpack.Huffman.Lowstar.Codec
module Dfa   = Hpack.Huffman.Lowstar.Dfa

let encode_len (src:B.buffer U8.t) (len:U32.t) : Stack U32.t
  (requires fun h -> B.live h src /\ B.length src == U32.v len /\ U32.v len < pow2 27)
  (ensures fun h0 r h1 -> B.modifies B.loc_none h0 h1)
  = Codec.encode_len src len

let encode (src:B.buffer U8.t) (len:U32.t) (dst:B.buffer U8.t) : Stack U32.t
  (requires fun h ->
    B.live h src /\ B.live h dst /\
    B.loc_disjoint (B.loc_buffer dst) (B.loc_buffer src) /\
    B.loc_disjoint (B.loc_buffer dst) (MB.loc_buffer huff_len) /\
    B.loc_disjoint (B.loc_buffer dst) (MB.loc_buffer huff_code) /\
    B.length src == U32.v len /\ U32.v len < pow2 27 /\ 4 * U32.v len + 1 <= B.length dst)
  (ensures fun h0 r h1 -> B.modifies (B.loc_buffer dst) h0 h1)
  = Codec.encode src len dst

let decode (src:B.buffer U8.t) (src_len:U32.t)
           (dst:B.buffer U8.t) (dst_cap:U32.t) (out_len:B.buffer U32.t) : Stack I32.t
  (requires fun h ->
    B.live h src /\ B.live h dst /\ B.live h out_len /\
    B.loc_disjoint (B.loc_buffer dst) (B.loc_buffer src) /\
    B.loc_disjoint (B.loc_buffer dst) (B.loc_buffer out_len) /\
    B.loc_disjoint (B.loc_buffer out_len) (B.loc_buffer src) /\
    B.length src == U32.v src_len /\ U32.v dst_cap <= B.length dst /\
    B.length out_len == 1 /\ U32.v src_len < pow2 27)
  (ensures fun h0 r h1 ->
    B.modifies (B.loc_union (B.loc_buffer dst) (B.loc_buffer out_len)) h0 h1)
  = Dfa.decode_dfa src src_len dst dst_cap out_len
