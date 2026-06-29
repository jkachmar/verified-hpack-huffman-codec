#!/usr/bin/env bash
# Build + run the C micro-benchmark against the committed verified C.
# No F*/krml toolchain needed — just a C compiler. Run from anywhere.
set -euo pipefail
cd "$(dirname "$0")/.."                      # repo root

CC="${CC:-cc}"
INC=(-Icbits -Icbits/generated -Icbits/generated/internal
     -Icbits/generated/krmllib/include -Icbits/generated/krmllib/minimal)
SRC=(cbits/hpack_huffman.c cbits/generated/Hpack_Huffman.c)

"$CC" -O2 -std=c11 "${INC[@]}" "${SRC[@]}" bench/bench_huffman.c -o bench/bench_huffman
./bench/bench_huffman
