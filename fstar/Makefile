# Verify (and extract C from) the F* HPACK Huffman spec & implementation.
#
# Run inside the project dev shell (`nix develop`), which provides `fstar.exe`
# and `krml`. The F* binary is `fstar.exe`, not `fstar`.
#
#   make verify    # type-check the whole proof (the full gate)
#   make generate  # verify+extract+vendor -> cbits/generated/ (one step)
#   make tables    # regenerate Hpack.Huffman.Lowstar.Tables.fst from the spec table
#   make clean     # drop the verification cache and extraction staging
#
# Layered modules (see ARCHITECTURE.md for the full proof map):
#   Foundations  Hpack.Huffman.{List,BitString,BinarySearch}  — generic, RFC-agnostic
#   Table        Hpack.Huffman.Table{,.Properties}            — RFC App. B data + invariants
#   Spec         Hpack.Huffman.Spec.{Codec,Lookup,RoundTrip,Decode,Dfa} — pure codec, round-trip, bit-view, DFA model
#   Refine       Hpack.Huffman.Refine.{Sort,Encode,Lookup,Decode,Dfa,RoundTrip} — tables == spec; codec bridges; DFA == decode_go; end-to-end round-trip
#   Lowstar      Hpack.Huffman.Lowstar.{Tables,DfaTables,Codec} — executable, lowered to C
#
# To regenerate the committed C after changing a .fst: `make generate`, then
# commit 'cbits/generated/'.

FSTAR     ?= fstar.exe
KRML      ?= krml
CACHE_DIR := .cache

# KaRaMeL home (the karamel `-home` Nix output): provides krmllib headers and
# the prebuilt .extract/*.krml library objects KaRaMeL needs to recognise
# proof-only ops (recall/witness/recall_contents) as no-ops. The dev shell
# should export KRML_HOME; `make extract` errors helpfully if it is unset.
KRML_HOME ?=

# Extraction roots. `Hpack.Huffman` is the public facade (the C ABI); it pulls in
# the codec and tables. KaRaMeL requires the bundle label to be a real module, so
# the facade names the bundle: every Hpack.Huffman.* module collapses into one
# `Hpack_Huffman.{c,h}` with the `Hpack_Huffman_*` symbol prefix the FFI shim calls.
EXTRACT_ROOT   := Hpack.Huffman
EXTRACT_CODEC  := Hpack.Huffman.Lowstar.Codec
EXTRACT_TABLES := Hpack.Huffman.Lowstar.Tables
EXTRACT_DFA    := Hpack.Huffman.Lowstar.Dfa
EXTRACT_DFATAB := Hpack.Huffman.Lowstar.DfaTables
BUNDLE         := Hpack.Huffman
BUNDLE_FILE    := Hpack_Huffman
EXTRACT_DIR    := extract

# Codegen directory that Cabal consumes, contains the generated C plus the
# vendored 'krmllib' runtime headers, so the normal build needs no F*/krml.
GENERATED_DIR := ../cbits/generated

# Cache our .checked files so re-verification is fast.
#
# Suppress benign warnings:
# * 241, cold-run missing '.checked'
# * 247, .checked not written when a krmllib dep's .checked is absent
# * 272, top-level effectful let (the immutable global tables)
# * 328, recursive-but-unused in Spec.Loops
FSTAR_FLAGS := --cache_checked_modules --cache_dir $(CACHE_DIR) --warn_error -241-247-272-328

.PHONY: all verify verify-spec verify-impl tables extract generate clean
all: verify

# Full gate: the pure spec proofs AND the Low*-adjacent proofs + implementation.
verify: verify-spec verify-impl

# Pure proofs (no krmllib): foundations, table invariants, and the round-trip.
# A successful run constitutes validation of the table data.
verify-spec:
	$(FSTAR) $(FSTAR_FLAGS) Hpack.Huffman.Util.List.fst
	$(FSTAR) $(FSTAR_FLAGS) Hpack.Huffman.Util.Bits.fst
	$(FSTAR) $(FSTAR_FLAGS) Hpack.Huffman.Table.fst
	$(FSTAR) $(FSTAR_FLAGS) Hpack.Huffman.Table.Properties.fst
	$(FSTAR) $(FSTAR_FLAGS) Hpack.Huffman.Spec.Codec.fst
	$(FSTAR) $(FSTAR_FLAGS) Hpack.Huffman.Spec.Lookup.fst
	$(FSTAR) $(FSTAR_FLAGS) Hpack.Huffman.Spec.RoundTrip.fst
	$(FSTAR) $(FSTAR_FLAGS) Hpack.Huffman.Spec.Decode.fst
	$(FSTAR) $(FSTAR_FLAGS) Hpack.Huffman.Spec.Dfa.fst

# Proofs that touch the executable tables (pull in krmllib: LowStar buffers,
# C.Loops): the generated tables, the refinement bridges, and the codec.
verify-impl:
	@test -n "$(KRML_HOME)" || { echo "ERROR: set KRML_HOME (karamel -home output) to verify the Low* modules"; exit 1; }
	$(FSTAR) $(FSTAR_FLAGS) --include $(KRML_HOME)/krmllib Hpack.Huffman.Lowstar.Tables.fst
	$(FSTAR) $(FSTAR_FLAGS) --include $(KRML_HOME)/krmllib Hpack.Huffman.Lowstar.DfaTables.fst
	$(FSTAR) $(FSTAR_FLAGS) --include $(KRML_HOME)/krmllib Hpack.Huffman.Refine.Encode.fst
	$(FSTAR) $(FSTAR_FLAGS) --include $(KRML_HOME)/krmllib Hpack.Huffman.Bridge.Decode.fst
	$(FSTAR) $(FSTAR_FLAGS) --include $(KRML_HOME)/krmllib Hpack.Huffman.Spec.DfaEquiv.fst
	$(FSTAR) $(FSTAR_FLAGS) --include $(KRML_HOME)/krmllib Hpack.Huffman.Refine.DfaTable.fst
	$(FSTAR) $(FSTAR_FLAGS) --include $(KRML_HOME)/krmllib Hpack.Huffman.Lowstar.Dfa.fst
	$(FSTAR) $(FSTAR_FLAGS) --include $(KRML_HOME)/krmllib Hpack.Huffman.Lowstar.Codec.fst
	$(FSTAR) $(FSTAR_FLAGS) --include $(KRML_HOME)/krmllib Hpack.Huffman.Lowstar.RoundTrip.fst
	$(FSTAR) $(FSTAR_FLAGS) --include $(KRML_HOME)/krmllib Hpack.Huffman.fst

# Regenerate the executable tables (Hpack.Huffman.Lowstar.Tables.fst) from the
# spec table (Hpack.Huffman.Table.fst). Runs from this directory; stages to a temp
# file so a generator error can't truncate the committed module. Regenerates both
# the encoder tables and the DFA transition table. After running, re-run
# `make generate` and commit the refreshed C.
tables:
	python3 gen_lowstar_tables.py > Hpack.Huffman.Lowstar.Tables.fst.tmp \
	  && mv Hpack.Huffman.Lowstar.Tables.fst.tmp Hpack.Huffman.Lowstar.Tables.fst
	python3 gen_dfa_tables.py > Hpack.Huffman.Lowstar.DfaTables.fst.tmp \
	  && mv Hpack.Huffman.Lowstar.DfaTables.fst.tmp Hpack.Huffman.Lowstar.DfaTables.fst

# Lower the verified Low* implementation to C. The `-bundle` label Hpack.Huffman
# (the facade) collapses every Hpack.Huffman.* module into one Hpack_Huffman.{c,h}
# with the Hpack_Huffman_* symbol prefix the FFI shim expects.
extract:
	@test -n "$(KRML_HOME)" || { echo "ERROR: set KRML_HOME (karamel -home output)"; exit 1; }
	rm -rf $(EXTRACT_DIR)
	rm -f *.krml
	# Two F* extraction passes, merged by krml. `Lowstar.Dfa` has an interface
	# (`.fsti`): F* emits its `.fst` bodies only when the `.fst` is an extraction
	# *root*, but it cannot be a root in the same invocation as the facade, which
	# depends on it *through* that interface (F* Error 117 — a root `.fst` would
	# break the abstraction its `.fsti` imposes on the facade). So:
	#   Pass A — roots = the DFA impl + its generated table; emits their bodies.
	$(FSTAR) $(FSTAR_FLAGS) --include $(KRML_HOME)/krmllib --codegen krml \
	  --extract '$(EXTRACT_DFA) $(EXTRACT_DFATAB)' $(EXTRACT_DFA).fst
	mv out.krml dfa.krml
	#   Pass B — root = the facade; the encode path + tables (`Lowstar.Dfa` stays an
	#   interface here, so `decode_dfa` is a prototype, linked to Pass A's body).
	$(FSTAR) $(FSTAR_FLAGS) --include $(KRML_HOME)/krmllib --codegen krml \
	  --extract '$(EXTRACT_ROOT) $(EXTRACT_CODEC) $(EXTRACT_TABLES)' $(EXTRACT_ROOT).fst
	$(KRML) -skip-compilation -ftail-calls \
	  -bundle '$(BUNDLE)=Hpack.Huffman.\*' \
	  $(KRML_HOME)/krmllib/.extract/*.krml *.krml \
	  -tmpdir $(EXTRACT_DIR) -warn-error +9-17

# Produce the committed cbits/generated/ tree from scratch:
# * extract the C
# * vendor it alongside the minimal 'krmllib' runtime headers
generate: extract
	@test -n "$(KRML_HOME)" || { echo "ERROR: set KRML_HOME (karamel -home output)"; exit 1; }
	rm -rf $(GENERATED_DIR)
	mkdir -p $(GENERATED_DIR)/internal $(GENERATED_DIR)/krmllib/include $(GENERATED_DIR)/krmllib/minimal
	cp $(EXTRACT_DIR)/$(BUNDLE_FILE).c $(EXTRACT_DIR)/$(BUNDLE_FILE).h $(GENERATED_DIR)/
	# KaRaMeL splits internal (static) declarations into internal/$(BUNDLE_FILE).h,
	# which the .c includes; vendor it alongside.
	cp $(EXTRACT_DIR)/internal/$(BUNDLE_FILE).h $(GENERATED_DIR)/internal/
	cp -R $(KRML_HOME)/include/. $(GENERATED_DIR)/krmllib/include/
	cp $(KRML_HOME)/krmllib/dist/minimal/*.h $(GENERATED_DIR)/krmllib/minimal/
	chmod -R u+w $(GENERATED_DIR)
	# Strip KaRaMeL's store-path-laden header from the generated files.
	python3 strip_header.py $(GENERATED_DIR)/$(BUNDLE_FILE).c $(GENERATED_DIR)/$(BUNDLE_FILE).h \
	  $(GENERATED_DIR)/internal/$(BUNDLE_FILE).h
	@echo "regenerated $(GENERATED_DIR)"

clean:
	rm -rf $(CACHE_DIR) *.krml $(EXTRACT_DIR)
