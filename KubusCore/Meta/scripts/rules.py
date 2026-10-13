#!/usr/bin/env python3
"""Parse the constructors of the minimal judgments (KubusCore/Meta/Minimal.lean): for each,
its name, binders, premises and conclusion. Used to generate proof skeletons."""
import re

def split_top(s, sep="→"):
    parts, depth, cur, i = [], 0, "", 0
    while i < len(s):
        c = s[i]
        if c in "([{⟨": depth += 1
        if c in ")]}⟩": depth -= 1
        if depth == 0 and s.startswith(sep, i):
            parts.append(cur.strip()); cur = ""; i += len(sep); continue
        cur += c; i += 1
    parts.append(cur.strip())
    return parts

def parse(path="KubusCore/Meta/Minimal.lean"):
    txt = open(path).read()
    i = txt.index("\nmutual\n")
    txt = txt[i:txt.index("\nend\n", i)]
    rules = []
    ind = None
    cur = None
    for ln in txt.split("\n"):
        m = re.match(r"inductive (\w+)", ln)
        if m:
            ind = m.group(1); continue
        m = re.match(r"  \| (\w+) (.*)", ln)
        if m and ind:
            cur = [ind, m.group(1), m.group(2)]
            rules.append(cur); continue
        if cur is not None and ln.startswith("      "):
            cur[2] += " " + ln.strip(); continue
        if not ln.startswith("      "):
            cur = None
    out = []
    for ind, name, sig in rules:
        # binders: leading {..} groups
        binders = []
        sig = sig.strip()
        while sig.startswith("{"):
            j = sig.index("}")
            binders += sig[1:j].split(":")[0].split()
            sig = sig[j+1:].strip()
        assert sig.startswith(":"), (name, sig)
        sig = sig[1:].strip()
        parts = split_top(sig)
        out.append(dict(ind=ind, name=name, binders=binders, prem=parts[:-1], concl=parts[-1]))
    return out

if __name__ == "__main__":
    for r in parse():
        print(r["ind"], r["name"], len(r["prem"]))
