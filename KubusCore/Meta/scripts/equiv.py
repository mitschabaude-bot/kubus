import sys
sys.path.insert(0,'/home/agent/code/kubus-meta/KubusCore/Meta/scripts')
from rules import parse
rs=parse('/home/agent/code/kubus-meta/KubusCore/Rules.lean')
fn={'HasTy':'toMin_ty','EqTm':'toMin_eq','Wf':'toMin_wf','HasTele':'toMin_tele','EqTele':'toMin_eqtele'}
min_ind={'HasTy':'HasTy0','EqTm':'EqTm0','Wf':'Wf0','HasTele':'HasTele0','EqTele':'EqTele0'}
def conv(p,h):
    for k in ['HasTy','EqTm','Wf','HasTele','EqTele']:
        if p.startswith(k+' '): return f"({fn[k]} {h})"
    return h
T=lambda h: f"(toMin_ty {h})"; E=lambda h: f"(toMin_eq {h})"
special = {
('HasTy','wk'): "HasTy0.wk hS (toMin_ty h0) (toMin_ty h1)",
('HasTy','dwk'): "HasTy0.dwk hS (toMin_ty h0)",
('HasTy','subst'): "HasTy0.subst hS (toMin_ty h0) (toMin_ty h1)",
('HasTy','dsubst'): "HasTy0.dsubst hS (toMin_ty h0) h1",
('HasTy','eqL'): "(hP (toMin_eq h0)).1",
('HasTy','eqR'): "(hP (toMin_eq h0)).2",
('HasTy','piDom'): "HasTy0.piDom hS (toMin_ty h0)",
('HasTy','piCod'): "HasTy0.piCod hS (toMin_ty h0)",
('HasTy','sigmaDom'): "HasTy0.sigmaDom hS (toMin_ty h0)",
('HasTy','sigmaCod'): "HasTy0.sigmaCod hS (toMin_ty h0)",
('HasTy','pathLine'): "HasTy0.pathLine hS (toMin_ty h0)",
('HasTy','pathLeft'): "HasTy0.pathLeft hS (toMin_ty h0)",
('HasTy','pathRight'): "HasTy0.pathRight hS (toMin_ty h0)",
('HasTy','ipiLine'): "HasTy0.ipiLine hS (toMin_ty h0)",
('HasTy','glueFib'): "HasTy0.glueFib hS (toMin_ty h0)",
('HasTy','ipi'): "HasTy0.ipi (wf_unshift hS (wf_of_ty (toMin_ty h0))) (toMin_ty h0)",
('HasTy','glueEl'): """by
      have g := toMin_ty h0
      obtain ⟨_, ⟨_, _, _, he⟩, _⟩ := gen_glue hS g rfl
      exact HasTy0.glueEl g he (toMin_ty h1) (toMin_ty h2) (toMin_eq h3)""",
('HasTy','con'): """by
      have hd := toMin_ty h3
      obtain ⟨D', hD', htele⟩ := gen_data_tele hd rfl
      rw [h0] at hD'; cases hD'
      exact HasTy0.con h0 h1 h2 hd htele (toMin_tele h4) h5 h6""",
('HasTy','elim'): """by
      have hd := toMin_ty h2
      obtain ⟨D', hD', htele⟩ := gen_data_tele hd rfl
      rw [h0] at hD'; cases hD'
      exact HasTy0.elim h0 h1 hd htele (toMin_ty h3) h4 h5
        (fun c C b a1 a2 => toMin_ty (h6 c C b a1 a2))
        (fun c C b k ψ e a1 a2 a3 => toMin_eq (h7 c C b k ψ e a1 a2 a3)) (toMin_ty h8)""",
('EqTm','wk'): "EqTm0.wk hS (toMin_ty h0) (toMin_eq h1)",
('EqTm','dwk'): "EqTm0.dwk hS (toMin_eq h0)",
('EqTm','dsubst'): "EqTm0.dsubst hS (toMin_eq h0) h1",
('EqTm','subst'): "EqTm0.subst hS (toMin_eq h0) (hP (toMin_eq h0)).2 (hP (toMin_eq h1)).1 (hP (toMin_eq h1)).2 (toMin_eq h1)",
('EqTm','face'): """by
      have ht := toMin_ty h2
      rcases valid_ty hS hP hT ht with ⟨l, hA⟩ | ⟨l, rfl⟩
      · exact EqTm0.face h0 h1 hA ht
      · exact EqTm0.faceU h0 h1 ht""",


('EqTm','ipi'): "EqTm0.ipi (wf_unshift hS (wf_of_eq (toMin_eq h0))) (toMin_eq h0)",
('EqTm','elim'): """EqTm0.elim h0 (toMin_ty h1) (toMin_ty h2) (toMin_eqtele h3) (toMin_eq h4) h5
        (fun c C b b' a1 a2 a3 => toMin_eq (h6 c C b b' a1 a2 a3)) (toMin_eq h7)""",
}
sigs={
'Wf':"theorem toMin_wf {Ψ Φ Γ} : Wf S Ψ Φ Γ → Wf0 S Ψ Φ Γ",
'HasTy':"theorem toMin_ty {Ψ Φ Γ t A} : HasTy S Ψ Φ Γ t A → HasTy0 S Ψ Φ Γ t A",
'HasTele':"theorem toMin_tele {Ψ Φ Γ ts Δ prev} : HasTele S Ψ Φ Γ ts Δ prev → HasTele0 S Ψ Φ Γ ts Δ prev",
'EqTele':"theorem toMin_eqtele {Ψ Φ Γ ts ts' Δ prev} : EqTele S Ψ Φ Γ ts ts' Δ prev → EqTele0 S Ψ Φ Γ ts ts' Δ prev",
'EqTm':"theorem toMin_eq {Ψ Φ Γ t u A} : EqTm S Ψ Φ Γ t u A → EqTm0 S Ψ Φ Γ t u A",
}
out=[]
for ind in ['Wf','HasTy','HasTele','EqTele','EqTm']:
    out.append(sigs[ind])
    for r in rs:
        if r['ind']!=ind: continue
        n=len(r['prem']); hs=" ".join(f"h{i}" for i in range(n))
        key=(ind,r['name'])
        if key in special: body=special[key]
        else:
            args=" ".join(conv(p,f"h{i}") for i,p in enumerate(r['prem']))
            body=f"{min_ind[ind]}.{r['name']} {args}".strip()
        out.append(f"  | .{r['name']} {hs} =>\n    {body}".replace(" .nil  =>"," .nil =>"))
    out.append("")
hdr='''import KubusCore.Meta.Valid

/-!
# Metatheory: the spec's judgments and the minimal judgments

`toMin_ty`/`toMin_eq`: every derivation of the spec is a derivation of the minimal judgments,
given presupposition for the minimal judgments (`Presup0`, needed for `eqL`/`eqR`, for
`EqTm.subst` with different terms, and for the type premise of the face rule) and typed
definitions (`SigTyped0`). The primitive weakening, substitution and inversion rules are
admissible (`Weaken.lean`, `Structural.lean`, `Inversion.lean`); the premises added by M1, M2,
M3, M6 are recovered by generation and validity. Conversely every minimal derivation is a
derivation of the spec (`toFull_ty`), since the minimal rules only add premises.
-/

namespace KubusCore.Meta

open Tm

variable {S : Sig}

section
variable (hS : SigClosed S) (hP : Presup0 S) (hT : SigTyped0 S)
include hS hP hT

mutual

'''
ftr='''end

end

end KubusCore.Meta
'''
open('/home/agent/code/kubus-meta/KubusCore/Meta/Equiv.lean','w').write(hdr+"\n".join(out)+ftr)

# ---------- minimal → full
rs0=parse('/home/agent/code/kubus-meta/KubusCore/Meta/Minimal.lean')
fn2={'HasTy0':'toFull_ty','EqTm0':'toFull_eq','Wf0':'toFull_wf','HasTele0':'toFull_tele','EqTele0':'toFull_eqtele'}
full_ind={'HasTy0':'HasTy','EqTm0':'EqTm','Wf0':'Wf','HasTele0':'HasTele','EqTele0':'EqTele'}
def conv2(p,h):
    for k in ['HasTy0','EqTm0','Wf0','HasTele0','EqTele0']:
        if p.startswith(k+' '): return f"({fn2[k]} {h})"
    return h
special2 = {
('HasTy0','ipi'): "HasTy.ipi (toFull_ty h1)",
('HasTy0','glueEl'): "HasTy.glueEl (toFull_ty h0) (toFull_ty h2) (toFull_ty h3) (toFull_eq h4)",
('HasTy0','con'): "HasTy.con h0 h1 h2 (toFull_ty h3) (toFull_tele h5) h6 h7",
('HasTy0','elim'): """HasTy.elim h0 h1 (toFull_ty h2) (toFull_ty h4) h5 h6
        (fun c C b a1 a2 => toFull_ty (h7 c C b a1 a2))
        (fun c C b k ψ e a1 a2 a3 => toFull_eq (h8 c C b k ψ e a1 a2 a3)) (toFull_ty h9)""",
('EqTm0','ipi'): "EqTm.ipi (toFull_eq h1)",
('EqTm0','face'): "EqTm.face h0 h1 (toFull_ty h3)",
('EqTm0','faceU'): "EqTm.face h0 h1 (toFull_ty h2)",
('EqTm0','elim'): """EqTm.elim h0 (toFull_ty h1) (toFull_ty h2) (toFull_eqtele h3) (toFull_eq h4) h5
        (fun c C b b' a1 a2 a3 => toFull_eq (h6 c C b b' a1 a2 a3)) (toFull_eq h7)""",
}
sigs2={
'Wf0':"theorem toFull_wf {Ψ Φ Γ} : Wf0 S Ψ Φ Γ → Wf S Ψ Φ Γ",
'HasTy0':"theorem toFull_ty {Ψ Φ Γ t A} : HasTy0 S Ψ Φ Γ t A → HasTy S Ψ Φ Γ t A",
'HasTele0':"theorem toFull_tele {Ψ Φ Γ ts Δ prev} : HasTele0 S Ψ Φ Γ ts Δ prev → HasTele S Ψ Φ Γ ts Δ prev",
'EqTele0':"theorem toFull_eqtele {Ψ Φ Γ ts ts' Δ prev} : EqTele0 S Ψ Φ Γ ts ts' Δ prev → EqTele S Ψ Φ Γ ts ts' Δ prev",
'EqTm0':"theorem toFull_eq {Ψ Φ Γ t u A} : EqTm0 S Ψ Φ Γ t u A → EqTm S Ψ Φ Γ t u A",
}
out2=[]
for ind in ['Wf0','HasTy0','HasTele0','EqTele0','EqTm0']:
    out2.append(sigs2[ind])
    for r in rs0:
        if r['ind']!=ind: continue
        n=len(r['prem']); hs=" ".join(f"h{i}" for i in range(n))
        key=(ind,r['name'])
        if key in special2: body=special2[key]
        else:
            args=" ".join(conv2(p,f"h{i}") for i,p in enumerate(r['prem']))
            body=f"{full_ind[ind]}.{r['name']} {args}".strip()
        out2.append(f"  | .{r['name']} {hs} =>\n    {body}")
    out2.append("")
hdr2='''
/-! ## The minimal judgments are derivable in the spec -/

mutual

'''
s=open('/home/agent/code/kubus-meta/KubusCore/Meta/Equiv.lean').read()
s=s.replace("\nend KubusCore.Meta\n", hdr2+"\n".join(out2)+"end\n\nend KubusCore.Meta\n")
open('/home/agent/code/kubus-meta/KubusCore/Meta/Equiv.lean','w').write(s)
