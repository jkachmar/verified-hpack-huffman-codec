# Verified HPACK Huffman Codec

> [!CAUTION]
> This project was intended mainly as an experiment in how far off the beaten
> path a programming language can be while still being amenable to LLM code
> generation.
>
> It's presented mainly as an example for others with similar interests, and
> to encourage me to audit the contents of this repository; don't use this for
> anything important in the meantime (or probably ever tbh).

A HPACK huffman codec (RFC 7541 §5.2 & Appendix B), written in F\*/Low\* and
lowered to C by [KaRaMeL](https://github.com/FStarLang/karamel).

Both encode & decode are proven correct, and the extracted C is competitive with
the reference codec extracted from `nghttp2`.

We take additional step of proving that the `nghttp2` 4-byte decode state
transition table is equivalent to the Huffman codes in RFC 7541.

## What's proven

- Encode: emits exactly the input's Huffman bit stream (i.e. each byte's
  Appendix B codeword, concatenated), then ≤7 all-ones padding bits to the next
  byte boundary.
- Decode: returns the exact RFC-decoded bytes on every valid stream; rejects
  all invalid streams.
- Round-trip: `decode(encode(x)) === x`.
- The `nghttp2`'s DFA transition table is proven cell-by-cell equal to the
  decoder specified as part of RFC 7541.

See [`ARCHITECTURE.md`](ARCHITECTURE.md) for the full proof-construction stack,
the trusted computing base, and the module map.

## Performance

The following benchmarks were performed on a 2024 M4 Max MacBook Pro:

| operation    | F* extraction  | nghttp2 baseline | ratio |
| ------------ | -------------- | ---------------- | ----- |
| encode 256 B | 237 ± 14 ns    | 231 ± 13 ns      | 1.03× |
| decode 256 B | 843 ± 52 ns    | 600 ± 54 ns      | 1.41× |

## Trusted computing base

Correctness rests on, the transcribed RFC table, KaRaMeL + its runtime headers,
the ~60-line C shim (`cbits/hpack_huffman.c`), and F\*/Z3.

The decode table and the executable arrays are generated and proven equal to
the specification.

## Using the codec (C)

This project's API is as follows:

```c
size_t hpack_huffman_encode_len(const uint8_t *src, size_t len);
size_t hpack_huffman_encode(const uint8_t *src, size_t len, uint8_t *dst);
int    hpack_huffman_decode(const uint8_t *src, size_t src_len,
                                     uint8_t *dst, size_t dst_cap, size_t *out_len);
```

...and can be depended upon by including the following directories:

* `cbits/generated`
  * the C code extracted from the proofs
* `cbits/generated/krmllib/include`
  * re-distributed `krmllib` headers
* `cbits/generated/krmllib/minimal`
  * re-distributed subset of `krmllib` C code

## Reproducing the verification

```sh
nix develop
make verify      # type-check the whole proof
make generate    # re-extract the verified C into cbits/generated/
```

## Testing & benchmarking

```sh
nix develop
make test
make bench
```

A C harness has been implemented to provide a minimal, toolchain-independent
sanity check & benchmark against a reference codec extracted from `nghttp2`.

## Layout

| path | what |
| ---- | ---- |
| `fstar/` | the F\* proof, table generators, `Makefile`, and `.fsti` interfaces |
| `cbits/hpack_huffman.{c,h}` | the C shim & public API |
| `cbits/generated/` | the KaRaMeL-extracted verified codec & vendored `krmllib` headers |
| `test/`, `bench/` | the C validation harness & micro-benchmark |

## License

[MPL-2.0](LICENSE). Prior-art attribution (nghttp2 — MIT; Pajarola) is in [`NOTICE`](NOTICE).
