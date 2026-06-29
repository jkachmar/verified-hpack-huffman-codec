#!/usr/bin/env python3
"""Replace KaRaMeL's auto-generated file header with a short, deterministic one.

KaRaMeL prepends a comment whose "invocation" line embeds the absolute Nix store
paths of every input .krml (~95 of them), which bloats the committed C and churns
on every toolchain bump. `make generate` runs this over the emitted C/H to swap
that block for a stable header.
"""
import sys

HEADER = (
    "/*\n"
    " * GENERATED from the verified F* sources in fstar/.\n"
    " * Do not edit by hand -- regenerate with: make -C fstar generate\n"
    " */\n"
)

for path in sys.argv[1:]:
    text = open(path).read()
    # The KaRaMeL header is the leading /* ... */ block; replace up to its close.
    end = text.index("*/") + 2
    rest = text[end:].lstrip("\n")
    open(path, "w").write(HEADER + "\n" + rest)
