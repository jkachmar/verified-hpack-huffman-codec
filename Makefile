# Top-level entry point. The F* proof build lives in fstar/Makefile (its commands
# resolve modules, the .cache, and the krml extraction staging relative to fstar/);
# this root Makefile delegates the proof targets there and owns the C harness.
#
#   make verify    — type-check the whole proof (the full gate; no admits)
#   make generate  — re-extract the verified C into cbits/generated/
#   make tables     — regenerate the executable tables from the spec table
#   make test       — build + run the C validation harness (round-trip, RFC, reject, diff)
#   make bench      — build + run the C micro-benchmark
#   make clean      — remove proof cache/staging and C harness binaries

.PHONY: all verify verify-spec verify-impl tables generate extract test bench clean

all: verify

verify verify-spec verify-impl tables generate extract:
	$(MAKE) -C fstar $@

test:
	./test/run.sh

bench:
	./bench/run.sh

clean:
	$(MAKE) -C fstar clean
	rm -f test/test_huffman test/test_diff bench/bench_huffman
