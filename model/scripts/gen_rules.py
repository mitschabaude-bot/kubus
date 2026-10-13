#!/usr/bin/env python3
"""Generate Model/Rules/*.lean skeleton data from KubusCore/Rules.lean.

Prints, for each constructor of Wf/HasTy/EqTm: (judgment, name, binders, premises, conclusion).
"""
import re, sys, json

src = open(sys.argv[1]).read()
# isolate the mutual block
start = src.index("inductive Wf")
end = src.index("\nend\n", start)
block = src[start:end]
rules = []
cur = None
for part in re.split(r"\ninductive ", "\n" + block):
    part = part.strip()
    if not part:
        continue
    head = part.split()[0]
    body = part[part.index("\n"):]
    # constructors start with "  | "
    ctors = re.split(r"\n  \| ", body)
    for c in ctors[1:]:
        # drop comments
        c = re.sub(r"/-.*?-/", "", c, flags=re.S)
        c = " ".join(c.split())
        m = re.match(r"(\w+) (\{[^}]*\})? ?: (.*)$", c)
        if not m:
            print("PARSE FAIL", c, file=sys.stderr); continue
        name, binders, ty = m.group(1), m.group(2) or "", m.group(3)
        # split on top-level arrows
        parts, depth, buf = [], 0, ""
        i = 0
        while i < len(ty):
            ch = ty[i]
            if ch in "([{": depth += 1
            if ch in ")]}": depth -= 1
            if depth == 0 and ty.startswith(" → ", i):
                parts.append(buf.strip()); buf = ""; i += 3; continue
            buf += ch; i += 1
        parts.append(buf.strip())
        rules.append(dict(judg=head, name=name, binders=binders, prem=parts[:-1], concl=parts[-1]))
json.dump(rules, sys.stdout, indent=1)
