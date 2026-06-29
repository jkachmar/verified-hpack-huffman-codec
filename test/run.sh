#!/usr/bin/env bash
# Build + run the C validation harness against the committed verified C.
# No F*/krml toolchain needed — just a C compiler. Run from anywhere.
set -euo pipefail
cd "$(dirname "$0")/.."                      # repo root

CC="${CC:-cc}"
INC=(-Icbits -Icbits/generated -Icbits/generated/internal
     -Icbits/generated/krmllib/include -Icbits/generated/krmllib/minimal)
SRC=(cbits/hpack_huffman.c cbits/generated/Hpack_Huffman.c)

echo "== building + running test/test_huffman =="
"$CC" -O2 -std=c11 "${INC[@]}" "${SRC[@]}" test/test_huffman.c -o test/test_huffman
./test/test_huffman

if [ -f test/test_diff.c ]; then
    echo "== building + running test/test_diff (differential vs reference decoder) =="
    "$CC" -O2 -std=c11 "${INC[@]}" "${SRC[@]}" test/ref_huffman.c test/test_diff.c -o test/test_diff
    ./test/test_diff
fi
