#!/usr/bin/env python3
"""Replace the `sorry` body of named lemmas in Model/Rules/Stubs.lean.
Usage: fill.py proofs.txt   where proofs.txt has blocks:
=== lemma_name
<proof lines, indented by 2>
"""
import sys, re
path = "Model/Rules/Stubs.lean"
s = open(path).read()
blocks = open(sys.argv[1]).read().split("=== ")[1:]
for b in blocks:
    name, _, body = b.partition("\n")
    name = name.strip()
    i = s.index(f"theorem {name} ")
    j = s.index(":= by\n  sorry\n", i)
    s = s[:j] + ":= by\n" + body.rstrip("\n") + "\n" + s[j + len(":= by\n  sorry\n"):]
open(path, "w").write(s)
