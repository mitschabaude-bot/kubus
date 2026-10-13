import sys
TAIL="\nnamespace KubusCore.Meta\n\ntheorem take_take_le {S : Sig} {k j : Nat} (hj : j ≤ k) : (S.take k).take j = S.take j := by\n  rw [List.take_take, Nat.min_eq_left hj]\n\ntheorem getElem?_take_some {S : Sig} {k j : Nat} {e : Entry} (h : (S.take k)[j]? = some e) :\n    j < k ∧ S[j]? = some e := by\n  have hj : j < k := by\n    have := (List.getElem?_eq_some_iff.1 h).1\n    simp [List.length_take] at this; omega\n  rw [List.getElem?_take_of_lt hj] at h\n  exact ⟨hj, h⟩\n\ntheorem wfSig_take {S : Sig} (h : WfSig S) (k : Nat) : WfSig (S.take k) := by\n  refine ⟨fun j t A hj => ?_, fun j D hj => ?_⟩\n  · obtain ⟨hjk, hj⟩ := getElem?_take_some hj\n    rw [take_take_le (Nat.le_of_lt hjk)]; exact h.1 j t A hj\n  · obtain ⟨hjk, hj⟩ := getElem?_take_some hj\n    rw [take_take_le (Nat.le_of_lt hjk)]; exact h.2 j D hj\n\n/-- The definitions of a well-formed signature are typed in the minimal judgments, given\n`ContractaTyped` for its prefixes. -/\ntheorem sigTyped0_of_wfSig : ∀ (n : Nat) (S : Sig), S.length = n → WfSig S →\n    (∀ k, ContractaTyped (S.take k)) → SigTyped0 S := by\n  intro n\n  induction n using Nat.strongRecOn with\n  | _ n ih =>\n    intro S hn hS hC k t A hk\n    have hklt : k < S.length := (List.getElem?_eq_some_iff.1 hk).1\n    have hwf := hS.1 k t A hk\n    have hS' := wfSig_take hS k\n    have hT' : SigTyped0 (S.take k) :=\n      ih k (by rw [← hn]; exact hklt) (S.take k) (by simp [List.length_take]; omega) hS'\n        (fun j => by rw [List.take_take]; exact hC _)\n    have hpre : ∀ (j : Nat) (e : Entry), (S.take k)[j]? = some e → S[j]? = some e :=\n      fun j e h => (getElem?_take_some h).2\n    obtain ⟨l, hA⟩ := hwf.2.2.1\n    exact ⟨⟨l, sigwk_ty hpre (spec_to_minimal_of hS' hT' (hC k) hA)⟩,\n      sigwk_ty hpre (spec_to_minimal_of hS' hT' (hC k) hwf.2.2.2)⟩\n\nend KubusCore.Meta\n"
sys.path.insert(0,'/home/agent/code/kubus-meta/KubusCore/Meta/scripts')
from rules import parse
rs=parse('/home/agent/code/kubus-meta/KubusCore/Meta/Minimal.lean')
fn={'HasTy0':'sigwk_ty','EqTm0':'sigwk_eq','Wf0':'sigwk_wf','HasTele0':'sigwk_tele','EqTele0':'sigwk_eqtele'}
def conv(p,h):
    for k in ['HasTy0','EqTm0','Wf0','HasTele0','EqTele0']:
        if p.startswith(k+' '): return f"({fn[k]} hpre {h})"
    if p.startswith('S[') and '= some' in p: return f"(hpre _ _ {h})"
    if p.startswith('(∀'):
        # count binders and hypotheses before the judgment
        inner=p[1:-1]
        head, rest = inner.split(',',1)
        nb = head.count('(') if '(' in head else len(head.split())-1
        import re
        binders = re.findall(r'\(([^:]*):', head)
        names = sum([b.split() for b in binders],[])
        # hypotheses: count top-level arrows in rest
        from rules import split_top
        parts = split_top(rest.strip())
        nh = len(parts)-1
        args = names + [f"a{i}" for i in range(nh)]
        judg = parts[-1]
        for k in ['HasTy0','EqTm0']:
            if judg.startswith(k+' '):
                return f"(fun {' '.join(args)} => {fn[k]} hpre ({h} {' '.join(args)}))"
        return h
    return h
sigs={
'Wf0':"theorem sigwk_wf {Ψ Φ Γ} : Wf0 S' Ψ Φ Γ → Wf0 S Ψ Φ Γ",
'HasTy0':"theorem sigwk_ty {Ψ Φ Γ t A} : HasTy0 S' Ψ Φ Γ t A → HasTy0 S Ψ Φ Γ t A",
'HasTele0':"theorem sigwk_tele {Ψ Φ Γ ts Δ prev} : HasTele0 S' Ψ Φ Γ ts Δ prev → HasTele0 S Ψ Φ Γ ts Δ prev",
'EqTele0':"theorem sigwk_eqtele {Ψ Φ Γ ts ts' Δ prev} : EqTele0 S' Ψ Φ Γ ts ts' Δ prev → EqTele0 S Ψ Φ Γ ts ts' Δ prev",
'EqTm0':"theorem sigwk_eq {Ψ Φ Γ t u A} : EqTm0 S' Ψ Φ Γ t u A → EqTm0 S Ψ Φ Γ t u A",
}
out=[]
for ind in ['Wf0','HasTy0','HasTele0','EqTele0','EqTm0']:
    out.append(sigs[ind].replace("theorem "+fn[ind]+" ", "theorem "+fn[ind]+" (hpre : ∀ (k : Nat) (e : Entry), S'[k]? = some e → S[k]? = some e) "))
    for r in rs:
        if r['ind']!=ind: continue
        n=len(r['prem']); hs=" ".join(f"h{i}" for i in range(n))
        args=" ".join(conv(p,f"h{i}") for i,p in enumerate(r['prem']))
        out.append(f"  | .{r['name']} {hs} => {ind}.{r['name']} {args}")
    out.append("")
hdr='''import KubusCore.Meta.Main

/-!
# Metatheory: weakening of the signature, and typed definitions

Judgments over a prefix of the signature hold over the signature. With the equivalence
theorem for the prefixes, the definitions of a well-formed signature are typed in the minimal
judgments (`sigTyped0_of_wfSig`).
-/

namespace KubusCore.Meta

open Tm

variable {S S' : Sig}

mutual

'''
open('/home/agent/code/kubus-meta/KubusCore/Meta/SigWk.lean','w').write(hdr+"\n".join(out)+"end\n\nend KubusCore.Meta\n"+TAIL)
