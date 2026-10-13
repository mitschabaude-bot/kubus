#!/usr/bin/env python3
"""Generate the soundness skeleton: one semantic lemma per rule (stubbed with `sorry`) and the
mutual soundness theorem. Usage: gen_stubs.py rules.json > out"""
import json, sys, re

rules = json.load(open(sys.argv[1]))
mode = sys.argv[2]  # "stubs" or "main"

def sem(s):
    s = re.sub(r"^HasTy S ", "SemTy S ", s)
    s = re.sub(r"^EqTm S ", "SemEq S ", s)
    s = re.sub(r"^Wf S ", "SemWf S ", s)
    return s

def kind(p):
    if p.startswith("HasTy S "): return "ty"
    if p.startswith("EqTm S "): return "eq"
    if p.startswith("Wf S "): return "wf"
    return None

needS = {("HasTy", "const"), ("EqTm", "delta")}

if mode == "stubs":
    for r in rules:
        nm = f"sem_{r['judg']}_{r['name']}"
        binders = r["binders"].replace("{", "{S : Sig} {", 1) if r["binders"] else "{S : Sig}"
        args = []
        if (r["judg"], r["name"]) in needS:
            args.append("(hS : SigOK S)")
        for i, p in enumerate(r["prem"]):
            args.append(f"(h{i} : {sem(p)})")
        print(f"theorem {nm} {binders}\n    {' '.join(args)} :\n    {sem(r['concl'])} := by\n  sorry\n")
else:
    names = {"Wf": "sound_wf", "HasTy": "sound_ty", "EqTm": "sound_eq"}
    concl = {
        "Wf": "{Ψ : ℕ} {Φ : I} {Γ : Ctx} : Wf S Ψ Φ Γ → SemWf S Ψ Φ Γ",
        "HasTy": "{Ψ : ℕ} {Φ : I} {Γ : Ctx} {t A : Tm} : HasTy S Ψ Φ Γ t A → SemTy S Ψ Φ Γ t A",
        "EqTm": "{Ψ : ℕ} {Φ : I} {Γ : Ctx} {t u A : Tm} : EqTm S Ψ Φ Γ t u A → SemEq S Ψ Φ Γ t u A",
    }
    print("mutual\n")
    for j in ["Wf", "HasTy", "EqTm"]:
        print(f"theorem {names[j]} {{S : Sig}} (hS : SigOK S) {concl[j]}")
        for r in rules:
            if r["judg"] != j: continue
            hs = [f"h{i}" for i in range(len(r["prem"]))]
            call = []
            if (r["judg"], r["name"]) in needS: call.append("hS")
            for i, p in enumerate(r["prem"]):
                k = kind(p)
                if k == "ty": call.append(f"(sound_ty hS h{i})")
                elif k == "eq": call.append(f"(sound_eq hS h{i})")
                elif k == "wf": call.append(f"(sound_wf hS h{i})")
                else: call.append(f"h{i}")
            print(f"  | .{r['name']} {' '.join(hs)} => sem_{r['judg']}_{r['name']} {' '.join(call)}")
        print()
    print("end")
