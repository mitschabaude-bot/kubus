import KubusCore.Meta.Valid

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

theorem toMin_wf {Ψ Φ Γ} : Wf S Ψ Φ Γ → Wf0 S Ψ Φ Γ
  | .nil h0 =>
    Wf0.nil h0
  | .cons h0 =>
    Wf0.cons (toMin_ty h0)

theorem toMin_ty {Ψ Φ Γ t A} : HasTy S Ψ Φ Γ t A → HasTy0 S Ψ Φ Γ t A
  | .var h0 h1 =>
    HasTy0.var (toMin_wf h0) h1
  | .conv h0 h1 =>
    HasTy0.conv (toMin_ty h0) (toMin_eq h1)
  | .restrict h0 h1 h2 =>
    HasTy0.restrict h0 h1 (toMin_ty h2)
  | .const h0 h1 =>
    HasTy0.const (toMin_wf h0) h1
  | .wk h0 h1 =>
    HasTy0.wk hS (toMin_ty h0) (toMin_ty h1)
  | .dwk h0 =>
    HasTy0.dwk hS (toMin_ty h0)
  | .subst h0 h1 =>
    HasTy0.subst hS (toMin_ty h0) (toMin_ty h1)
  | .dsubst h0 h1 =>
    HasTy0.dsubst hS (toMin_ty h0) h1
  | .eqL h0 =>
    (hP (toMin_eq h0)).1
  | .eqR h0 =>
    (hP (toMin_eq h0)).2
  | .piDom h0 =>
    HasTy0.piDom hS (toMin_ty h0)
  | .piCod h0 =>
    HasTy0.piCod hS (toMin_ty h0)
  | .sigmaDom h0 =>
    HasTy0.sigmaDom hS (toMin_ty h0)
  | .sigmaCod h0 =>
    HasTy0.sigmaCod hS (toMin_ty h0)
  | .pathLine h0 =>
    HasTy0.pathLine hS (toMin_ty h0)
  | .pathLeft h0 =>
    HasTy0.pathLeft hS (toMin_ty h0)
  | .pathRight h0 =>
    HasTy0.pathRight hS (toMin_ty h0)
  | .glueFib h0 =>
    HasTy0.glueFib hS (toMin_ty h0)
  | .univ h0 h1 =>
    HasTy0.univ h0 (toMin_wf h1)
  | .cumul h0 h1 =>
    HasTy0.cumul h0 (toMin_ty h1)
  | .pi h0 h1 =>
    HasTy0.pi (toMin_ty h0) (toMin_ty h1)
  | .lam h0 h1 =>
    HasTy0.lam (toMin_ty h0) (toMin_ty h1)
  | .app h0 h1 =>
    HasTy0.app (toMin_ty h0) (toMin_ty h1)
  | .sigma h0 h1 =>
    HasTy0.sigma (toMin_ty h0) (toMin_ty h1)
  | .pair h0 h1 h2 =>
    HasTy0.pair (toMin_ty h0) (toMin_ty h1) (toMin_ty h2)
  | .fst h0 =>
    HasTy0.fst (toMin_ty h0)
  | .snd h0 =>
    HasTy0.snd (toMin_ty h0)
  | .path h0 h1 h2 =>
    HasTy0.path (toMin_ty h0) (toMin_ty h1) (toMin_ty h2)
  | .plam h0 h1 h2 h3 =>
    HasTy0.plam (toMin_ty h0) (toMin_ty h1) (toMin_eq h2) (toMin_eq h3)
  | .papp h0 h1 =>
    HasTy0.papp (toMin_ty h0) h1
  | .ipi h0 =>
    HasTy0.ipi (wf_unshift hS (wf_of_ty (toMin_ty h0))) (toMin_ty h0)
  | .ilam h0 h1 =>
    HasTy0.ilam (toMin_ty h0) (toMin_ty h1)
  | .iapp h0 h1 =>
    HasTy0.iapp (toMin_ty h0) h1
  | .ipiLine h0 =>
    HasTy0.ipiLine hS (toMin_ty h0)
  | .split h0 h1 h2 h3 h4 h5 h6 =>
    HasTy0.split h0 h1 h2 (toMin_ty h3) (toMin_ty h4) (toMin_ty h5) (toMin_eq h6)
  | .abort h0 h1 =>
    HasTy0.abort h0 (toMin_ty h1)
  | .transp h0 h1 h2 h3 =>
    HasTy0.transp (toMin_ty h0) h1 (toMin_eq h2) (toMin_ty h3)
  | .hcomp h0 h1 h2 h3 h4 =>
    HasTy0.hcomp (toMin_ty h0) h1 (toMin_ty h2) (toMin_ty h3) (toMin_eq h4)
  | .glue h0 h1 h2 h3 =>
    HasTy0.glue (toMin_ty h0) h1 (toMin_ty h2) (toMin_ty h3)
  | .glueEl h0 h1 h2 h3 =>
    by
      have g := toMin_ty h0
      obtain ⟨_, ⟨_, _, _, he⟩, _⟩ := gen_glue hS g rfl
      exact HasTy0.glueEl g he (toMin_ty h1) (toMin_ty h2) (toMin_eq h3)
  | .unglue h0 h1 h2 h3 =>
    HasTy0.unglue (toMin_ty h0) (toMin_ty h1) (toMin_ty h2) (toMin_ty h3)
  | .data h0 h1 h2 =>
    HasTy0.data h0 h1 (toMin_tele h2)
  | .con h0 h1 h2 h3 h4 h5 h6 =>
    by
      have hd := toMin_ty h3
      obtain ⟨D', hD', htele⟩ := gen_data_tele hd rfl
      rw [h0] at hD'; cases hD'
      exact HasTy0.con h0 h1 h2 hd htele (toMin_tele h4) h5 h6
  | .elim h0 h1 h2 h3 h4 h5 h6 h7 h8 =>
    by
      have hd := toMin_ty h2
      obtain ⟨D', hD', htele⟩ := gen_data_tele hd rfl
      rw [h0] at hD'; cases hD'
      exact HasTy0.elim h0 h1 hd htele (toMin_ty h3) h4 h5
        (fun c C b a1 a2 => toMin_ty (h6 c C b a1 a2))
        (fun c C b k ψ e a1 a2 a3 => toMin_eq (h7 c C b k ψ e a1 a2 a3)) (toMin_ty h8)

theorem toMin_tele {Ψ Φ Γ ts Δ prev} : HasTele S Ψ Φ Γ ts Δ prev → HasTele0 S Ψ Φ Γ ts Δ prev
  | .nil h0 =>
    HasTele0.nil (toMin_wf h0)
  | .cons h0 h1 =>
    HasTele0.cons (toMin_ty h0) (toMin_tele h1)

theorem toMin_eqtele {Ψ Φ Γ ts ts' Δ prev} : EqTele S Ψ Φ Γ ts ts' Δ prev → EqTele0 S Ψ Φ Γ ts ts' Δ prev
  | .nil h0 =>
    EqTele0.nil (toMin_wf h0)
  | .cons h0 h1 =>
    EqTele0.cons (toMin_eq h0) (toMin_eqtele h1)
  | .dataInj h0 h1 h2 h3 =>
    EqTele0.dataInj h0 (toMin_tele h1) (toMin_tele h2) (toMin_eq h3)

theorem toMin_eq {Ψ Φ Γ t u A} : EqTm S Ψ Φ Γ t u A → EqTm0 S Ψ Φ Γ t u A
  | .refl h0 =>
    EqTm0.refl (toMin_ty h0)
  | .symm h0 =>
    EqTm0.symm (toMin_eq h0)
  | .trans h0 h1 =>
    EqTm0.trans (toMin_eq h0) (toMin_eq h1)
  | .conv h0 h1 =>
    EqTm0.conv (toMin_eq h0) (toMin_eq h1)
  | .restrict h0 h1 h2 =>
    EqTm0.restrict h0 h1 (toMin_eq h2)
  | .cumul h0 h1 =>
    EqTm0.cumul h0 (toMin_eq h1)
  | .wk h0 h1 =>
    EqTm0.wk hS (toMin_ty h0) (toMin_eq h1)
  | .dwk h0 =>
    EqTm0.dwk hS (toMin_eq h0)
  | .subst h0 h1 =>
    EqTm0.subst hS (toMin_eq h0) (hP (toMin_eq h0)).2 (hP (toMin_eq h1)).1 (hP (toMin_eq h1)).2 (toMin_eq h1)
  | .dsubst h0 h1 =>
    EqTm0.dsubst hS (toMin_eq h0) h1
  | .delta h0 h1 =>
    EqTm0.delta (toMin_ty h0) h1
  | .absurd h0 h1 h2 =>
    EqTm0.absurd h0 (toMin_ty h1) (toMin_ty h2)
  | .local h0 h1 h2 h3 h4 h5 h6 =>
    EqTm0.local h0 h1 h2 (toMin_ty h3) (toMin_ty h4) (toMin_eq h5) (toMin_eq h6)
  | .face h0 h1 h2 =>
    by
      have ht := toMin_ty h2
      rcases valid_ty hS hP hT ht with ⟨l, hA⟩ | ⟨l, rfl⟩
      · exact EqTm0.face h0 h1 hA ht
      · exact EqTm0.faceU h0 h1 ht
  | .pi h0 h1 =>
    EqTm0.pi (toMin_eq h0) (toMin_eq h1)
  | .lam h0 h1 =>
    EqTm0.lam (toMin_ty h0) (toMin_eq h1)
  | .app h0 h1 =>
    EqTm0.app (toMin_eq h0) (toMin_eq h1)
  | .sigma h0 h1 =>
    EqTm0.sigma (toMin_eq h0) (toMin_eq h1)
  | .pair h0 h1 h2 =>
    EqTm0.pair (toMin_ty h0) (toMin_eq h1) (toMin_eq h2)
  | .fst h0 =>
    EqTm0.fst (toMin_eq h0)
  | .snd h0 =>
    EqTm0.snd (toMin_eq h0)
  | .path h0 h1 h2 =>
    EqTm0.path (toMin_eq h0) (toMin_eq h1) (toMin_eq h2)
  | .plam h0 h1 h2 h3 =>
    EqTm0.plam (toMin_ty h0) (toMin_ty h1) (toMin_ty h2) (toMin_eq h3)
  | .papp h0 h1 h2 h3 =>
    EqTm0.papp (toMin_eq h0) h1 h2 h3
  | .split h0 h1 h2 h3 =>
    EqTm0.split (toMin_ty h0) (toMin_ty h1) (toMin_eq h2) (toMin_eq h3)
  | .transp h0 h1 h2 h3 h4 h5 =>
    EqTm0.transp (toMin_ty h0) (toMin_ty h1) (toMin_eq h2) h3 h4 (toMin_eq h5)
  | .hcomp h0 h1 h2 h3 h4 h5 h6 =>
    EqTm0.hcomp (toMin_ty h0) (toMin_ty h1) (toMin_eq h2) h3 h4 (toMin_eq h5) (toMin_eq h6)
  | .glue h0 h1 h2 h3 h4 h5 h6 =>
    EqTm0.glue (toMin_ty h0) (toMin_ty h1) (toMin_eq h2) h3 h4 (toMin_eq h5) (toMin_eq h6)
  | .glueEl h0 h1 h2 h3 h4 h5 h6 =>
    EqTm0.glueEl (toMin_ty h0) (toMin_ty h1) h2 h3 (toMin_eq h4) (toMin_eq h5) (toMin_eq h6)
  | .unglue h0 h1 h2 h3 h4 h5 =>
    EqTm0.unglue (toMin_ty h0) (toMin_ty h1) h2 h3 (toMin_eq h4) (toMin_eq h5)
  | .ipi h0 =>
    EqTm0.ipi (wf_unshift hS (wf_of_eq (toMin_eq h0))) (toMin_eq h0)
  | .ilam h0 h1 =>
    EqTm0.ilam (toMin_ty h0) (toMin_eq h1)
  | .iapp h0 h1 h2 h3 =>
    EqTm0.iapp (toMin_eq h0) h1 h2 h3
  | .piInjDom h0 =>
    EqTm0.piInjDom (toMin_eq h0)
  | .piInjCod h0 h1 =>
    EqTm0.piInjCod (toMin_eq h0) (toMin_ty h1)
  | .sigmaInjDom h0 =>
    EqTm0.sigmaInjDom (toMin_eq h0)
  | .sigmaInjCod h0 h1 =>
    EqTm0.sigmaInjCod (toMin_eq h0) (toMin_ty h1)
  | .pathInjLine h0 h1 =>
    EqTm0.pathInjLine (toMin_eq h0) h1
  | .pathInjLeft h0 =>
    EqTm0.pathInjLeft (toMin_eq h0)
  | .pathInjRight h0 =>
    EqTm0.pathInjRight (toMin_eq h0)
  | .ipiInj h0 h1 =>
    EqTm0.ipiInj (toMin_eq h0) h1
  | .noConf h0 h1 h2 h3 =>
    EqTm0.noConf h0 (toMin_eq h1) (toMin_ty h2) (toMin_ty h3)
  | .piBeta h0 =>
    EqTm0.piBeta (toMin_ty h0)
  | .piEta h0 =>
    EqTm0.piEta (toMin_ty h0)
  | .fstBeta h0 =>
    EqTm0.fstBeta (toMin_ty h0)
  | .sndBeta h0 =>
    EqTm0.sndBeta (toMin_ty h0)
  | .sigmaEta h0 =>
    EqTm0.sigmaEta (toMin_ty h0)
  | .pathBeta h0 =>
    EqTm0.pathBeta (toMin_ty h0)
  | .pathEta h0 =>
    EqTm0.pathEta (toMin_ty h0)
  | .ipiEta h0 =>
    EqTm0.ipiEta (toMin_ty h0)
  | .pathZero h0 =>
    EqTm0.pathZero (toMin_ty h0)
  | .pathOne h0 =>
    EqTm0.pathOne (toMin_ty h0)
  | .splitL h0 h1 =>
    EqTm0.splitL h0 (toMin_ty h1)
  | .splitR h0 h1 =>
    EqTm0.splitR h0 (toMin_ty h1)
  | .transpFace h0 h1 =>
    EqTm0.transpFace h0 (toMin_ty h1)
  | .hcompFace h0 h1 =>
    EqTm0.hcompFace h0 (toMin_ty h1)
  | .transpU h0 =>
    EqTm0.transpU (toMin_ty h0)
  | .transpPi h0 =>
    EqTm0.transpPi (toMin_ty h0)
  | .transpSigma h0 =>
    EqTm0.transpSigma (toMin_ty h0)
  | .transpPath h0 =>
    EqTm0.transpPath (toMin_ty h0)
  | .transpGlue h0 h1 h2 h3 h4 h5 =>
    EqTm0.transpGlue (toMin_ty h0) (toMin_ty h1) (toMin_ty h2) h3 h4 h5
  | .transpIPi h0 =>
    EqTm0.transpIPi (toMin_ty h0)
  | .hcompIPi h0 =>
    EqTm0.hcompIPi (toMin_ty h0)
  | .hcompPi h0 =>
    EqTm0.hcompPi (toMin_ty h0)
  | .hcompSigma h0 =>
    EqTm0.hcompSigma (toMin_ty h0)
  | .hcompPath h0 =>
    EqTm0.hcompPath (toMin_ty h0)
  | .hcompGlue h0 h1 h2 =>
    EqTm0.hcompGlue (toMin_ty h0) (toMin_ty h1) (toMin_ty h2)
  | .hcompU h0 =>
    EqTm0.hcompU (toMin_ty h0)
  | .glueFace h0 h1 =>
    EqTm0.glueFace h0 (toMin_ty h1)
  | .glueElFace h0 h1 =>
    EqTm0.glueElFace h0 (toMin_ty h1)
  | .unglueFace h0 h1 h2 h3 =>
    EqTm0.unglueFace h0 (toMin_ty h1) (toMin_ty h2) (toMin_ty h3)
  | .glueBeta h0 h1 =>
    EqTm0.glueBeta (toMin_ty h0) (toMin_ty h1)
  | .glueEta h0 =>
    EqTm0.glueEta (toMin_ty h0)
  | .data h0 h1 h2 h3 =>
    EqTm0.data h0 (toMin_ty h1) (toMin_ty h2) (toMin_eqtele h3)
  | .con h0 h1 h2 h3 h4 h5 h6 h7 =>
    EqTm0.con h0 h1 (toMin_ty h2) (toMin_ty h3) (toMin_eqtele h4) (toMin_eqtele h5) h6 h7
  | .elim h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 =>
    EqTm0.elim h0 (toMin_ty h1) (toMin_ty h2) (toMin_eqtele h3) (toMin_eq h4) h5 h6 h7
        (fun c C b b' a1 a2 a3 => toMin_eq (h8 c C b b' a1 a2 a3)) (toMin_eq h9)
  | .conBnd h0 h1 h2 h3 h4 h5 h6 =>
    EqTm0.conBnd h0 h1 h2 h3 h4 h5 (toMin_ty h6)
  | .elimCon h0 h1 h2 h3 h4 h5 h6 h7 =>
    EqTm0.elimCon h0 h1 h2 h3 h4 h5 (toMin_tele h6) (toMin_ty h7)
  | .elimHcomp h0 h1 h2 =>
    EqTm0.elimHcomp h0 (toMin_ty h1) (toMin_ty h2)
  | .transpData0 h0 h1 h2 =>
    EqTm0.transpData0 h0 h1 (toMin_ty h2)
  | .transpCon h0 h1 h2 h3 h4 h5 h6 =>
    EqTm0.transpCon h0 h1 h2 h3 h4 (toMin_tele h5) (toMin_ty h6)
  | .transpHcomp h0 h1 h2 h3 =>
    EqTm0.transpHcomp h0 h1 (toMin_ty h2) (toMin_ty h3)
end

end

/-! ## The minimal judgments are derivable in the spec -/

mutual

theorem toFull_wf {Ψ Φ Γ} : Wf0 S Ψ Φ Γ → Wf S Ψ Φ Γ
  | .nil h0 =>
    Wf.nil h0
  | .cons h0 =>
    Wf.cons (toFull_ty h0)

theorem toFull_ty {Ψ Φ Γ t A} : HasTy0 S Ψ Φ Γ t A → HasTy S Ψ Φ Γ t A
  | .var h0 h1 =>
    HasTy.var (toFull_wf h0) h1
  | .conv h0 h1 =>
    HasTy.conv (toFull_ty h0) (toFull_eq h1)
  | .restrict h0 h1 h2 =>
    HasTy.restrict h0 h1 (toFull_ty h2)
  | .const h0 h1 =>
    HasTy.const (toFull_wf h0) h1
  | .univ h0 h1 =>
    HasTy.univ h0 (toFull_wf h1)
  | .cumul h0 h1 =>
    HasTy.cumul h0 (toFull_ty h1)
  | .pi h0 h1 =>
    HasTy.pi (toFull_ty h0) (toFull_ty h1)
  | .lam h0 h1 =>
    HasTy.lam (toFull_ty h0) (toFull_ty h1)
  | .app h0 h1 =>
    HasTy.app (toFull_ty h0) (toFull_ty h1)
  | .sigma h0 h1 =>
    HasTy.sigma (toFull_ty h0) (toFull_ty h1)
  | .pair h0 h1 h2 =>
    HasTy.pair (toFull_ty h0) (toFull_ty h1) (toFull_ty h2)
  | .fst h0 =>
    HasTy.fst (toFull_ty h0)
  | .snd h0 =>
    HasTy.snd (toFull_ty h0)
  | .path h0 h1 h2 =>
    HasTy.path (toFull_ty h0) (toFull_ty h1) (toFull_ty h2)
  | .plam h0 h1 h2 h3 =>
    HasTy.plam (toFull_ty h0) (toFull_ty h1) (toFull_eq h2) (toFull_eq h3)
  | .papp h0 h1 =>
    HasTy.papp (toFull_ty h0) h1
  | .ipi h0 h1 =>
    HasTy.ipi (toFull_ty h1)
  | .ilam h0 h1 =>
    HasTy.ilam (toFull_ty h0) (toFull_ty h1)
  | .iapp h0 h1 =>
    HasTy.iapp (toFull_ty h0) h1
  | .split h0 h1 h2 h3 h4 h5 h6 =>
    HasTy.split h0 h1 h2 (toFull_ty h3) (toFull_ty h4) (toFull_ty h5) (toFull_eq h6)
  | .abort h0 h1 =>
    HasTy.abort h0 (toFull_ty h1)
  | .transp h0 h1 h2 h3 =>
    HasTy.transp (toFull_ty h0) h1 (toFull_eq h2) (toFull_ty h3)
  | .hcomp h0 h1 h2 h3 h4 =>
    HasTy.hcomp (toFull_ty h0) h1 (toFull_ty h2) (toFull_ty h3) (toFull_eq h4)
  | .glue h0 h1 h2 h3 =>
    HasTy.glue (toFull_ty h0) h1 (toFull_ty h2) (toFull_ty h3)
  | .glueEl h0 h1 h2 h3 h4 =>
    HasTy.glueEl (toFull_ty h0) (toFull_ty h2) (toFull_ty h3) (toFull_eq h4)
  | .unglue h0 h1 h2 h3 =>
    HasTy.unglue (toFull_ty h0) (toFull_ty h1) (toFull_ty h2) (toFull_ty h3)
  | .data h0 h1 h2 =>
    HasTy.data h0 h1 (toFull_tele h2)
  | .con h0 h1 h2 h3 h4 h5 h6 h7 =>
    HasTy.con h0 h1 h2 (toFull_ty h3) (toFull_tele h5) h6 h7
  | .elim h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 =>
    HasTy.elim h0 h1 (toFull_ty h2) (toFull_ty h4) h5 h6
        (fun c C b a1 a2 => toFull_ty (h7 c C b a1 a2))
        (fun c C b k ψ e a1 a2 a3 => toFull_eq (h8 c C b k ψ e a1 a2 a3)) (toFull_ty h9)

theorem toFull_tele {Ψ Φ Γ ts Δ prev} : HasTele0 S Ψ Φ Γ ts Δ prev → HasTele S Ψ Φ Γ ts Δ prev
  | .nil h0 =>
    HasTele.nil (toFull_wf h0)
  | .cons h0 h1 =>
    HasTele.cons (toFull_ty h0) (toFull_tele h1)

theorem toFull_eqtele {Ψ Φ Γ ts ts' Δ prev} : EqTele0 S Ψ Φ Γ ts ts' Δ prev → EqTele S Ψ Φ Γ ts ts' Δ prev
  | .nil h0 =>
    EqTele.nil (toFull_wf h0)
  | .cons h0 h1 =>
    EqTele.cons (toFull_eq h0) (toFull_eqtele h1)
  | .dataInj h0 h1 h2 h3 =>
    EqTele.dataInj h0 (toFull_tele h1) (toFull_tele h2) (toFull_eq h3)

theorem toFull_eq {Ψ Φ Γ t u A} : EqTm0 S Ψ Φ Γ t u A → EqTm S Ψ Φ Γ t u A
  | .refl h0 =>
    EqTm.refl (toFull_ty h0)
  | .symm h0 =>
    EqTm.symm (toFull_eq h0)
  | .trans h0 h1 =>
    EqTm.trans (toFull_eq h0) (toFull_eq h1)
  | .conv h0 h1 =>
    EqTm.conv (toFull_eq h0) (toFull_eq h1)
  | .restrict h0 h1 h2 =>
    EqTm.restrict h0 h1 (toFull_eq h2)
  | .cumul h0 h1 =>
    EqTm.cumul h0 (toFull_eq h1)
  | .delta h0 h1 =>
    EqTm.delta (toFull_ty h0) h1
  | .absurd h0 h1 h2 =>
    EqTm.absurd h0 (toFull_ty h1) (toFull_ty h2)
  | .local h0 h1 h2 h3 h4 h5 h6 =>
    EqTm.local h0 h1 h2 (toFull_ty h3) (toFull_ty h4) (toFull_eq h5) (toFull_eq h6)
  | .face h0 h1 h2 h3 =>
    EqTm.face h0 h1 (toFull_ty h3)
  | .faceU h0 h1 h2 =>
    EqTm.face h0 h1 (toFull_ty h2)
  | .pi h0 h1 =>
    EqTm.pi (toFull_eq h0) (toFull_eq h1)
  | .lam h0 h1 =>
    EqTm.lam (toFull_ty h0) (toFull_eq h1)
  | .app h0 h1 =>
    EqTm.app (toFull_eq h0) (toFull_eq h1)
  | .sigma h0 h1 =>
    EqTm.sigma (toFull_eq h0) (toFull_eq h1)
  | .pair h0 h1 h2 =>
    EqTm.pair (toFull_ty h0) (toFull_eq h1) (toFull_eq h2)
  | .fst h0 =>
    EqTm.fst (toFull_eq h0)
  | .snd h0 =>
    EqTm.snd (toFull_eq h0)
  | .path h0 h1 h2 =>
    EqTm.path (toFull_eq h0) (toFull_eq h1) (toFull_eq h2)
  | .plam h0 h1 h2 h3 =>
    EqTm.plam (toFull_ty h0) (toFull_ty h1) (toFull_ty h2) (toFull_eq h3)
  | .papp h0 h1 h2 h3 =>
    EqTm.papp (toFull_eq h0) h1 h2 h3
  | .split h0 h1 h2 h3 =>
    EqTm.split (toFull_ty h0) (toFull_ty h1) (toFull_eq h2) (toFull_eq h3)
  | .transp h0 h1 h2 h3 h4 h5 =>
    EqTm.transp (toFull_ty h0) (toFull_ty h1) (toFull_eq h2) h3 h4 (toFull_eq h5)
  | .hcomp h0 h1 h2 h3 h4 h5 h6 =>
    EqTm.hcomp (toFull_ty h0) (toFull_ty h1) (toFull_eq h2) h3 h4 (toFull_eq h5) (toFull_eq h6)
  | .glue h0 h1 h2 h3 h4 h5 h6 =>
    EqTm.glue (toFull_ty h0) (toFull_ty h1) (toFull_eq h2) h3 h4 (toFull_eq h5) (toFull_eq h6)
  | .glueEl h0 h1 h2 h3 h4 h5 h6 =>
    EqTm.glueEl (toFull_ty h0) (toFull_ty h1) h2 h3 (toFull_eq h4) (toFull_eq h5) (toFull_eq h6)
  | .unglue h0 h1 h2 h3 h4 h5 =>
    EqTm.unglue (toFull_ty h0) (toFull_ty h1) h2 h3 (toFull_eq h4) (toFull_eq h5)
  | .ipi h0 h1 =>
    EqTm.ipi (toFull_eq h1)
  | .ilam h0 h1 =>
    EqTm.ilam (toFull_ty h0) (toFull_eq h1)
  | .iapp h0 h1 h2 h3 =>
    EqTm.iapp (toFull_eq h0) h1 h2 h3
  | .piInjDom h0 =>
    EqTm.piInjDom (toFull_eq h0)
  | .piInjCod h0 h1 =>
    EqTm.piInjCod (toFull_eq h0) (toFull_ty h1)
  | .sigmaInjDom h0 =>
    EqTm.sigmaInjDom (toFull_eq h0)
  | .sigmaInjCod h0 h1 =>
    EqTm.sigmaInjCod (toFull_eq h0) (toFull_ty h1)
  | .pathInjLine h0 h1 =>
    EqTm.pathInjLine (toFull_eq h0) h1
  | .pathInjLeft h0 =>
    EqTm.pathInjLeft (toFull_eq h0)
  | .pathInjRight h0 =>
    EqTm.pathInjRight (toFull_eq h0)
  | .ipiInj h0 h1 =>
    EqTm.ipiInj (toFull_eq h0) h1
  | .noConf h0 h1 h2 h3 =>
    EqTm.noConf h0 (toFull_eq h1) (toFull_ty h2) (toFull_ty h3)
  | .piBeta h0 =>
    EqTm.piBeta (toFull_ty h0)
  | .piEta h0 =>
    EqTm.piEta (toFull_ty h0)
  | .fstBeta h0 =>
    EqTm.fstBeta (toFull_ty h0)
  | .sndBeta h0 =>
    EqTm.sndBeta (toFull_ty h0)
  | .sigmaEta h0 =>
    EqTm.sigmaEta (toFull_ty h0)
  | .pathBeta h0 =>
    EqTm.pathBeta (toFull_ty h0)
  | .pathEta h0 =>
    EqTm.pathEta (toFull_ty h0)
  | .ipiEta h0 =>
    EqTm.ipiEta (toFull_ty h0)
  | .pathZero h0 =>
    EqTm.pathZero (toFull_ty h0)
  | .pathOne h0 =>
    EqTm.pathOne (toFull_ty h0)
  | .splitL h0 h1 =>
    EqTm.splitL h0 (toFull_ty h1)
  | .splitR h0 h1 =>
    EqTm.splitR h0 (toFull_ty h1)
  | .transpFace h0 h1 =>
    EqTm.transpFace h0 (toFull_ty h1)
  | .hcompFace h0 h1 =>
    EqTm.hcompFace h0 (toFull_ty h1)
  | .transpU h0 =>
    EqTm.transpU (toFull_ty h0)
  | .transpPi h0 =>
    EqTm.transpPi (toFull_ty h0)
  | .transpSigma h0 =>
    EqTm.transpSigma (toFull_ty h0)
  | .transpPath h0 =>
    EqTm.transpPath (toFull_ty h0)
  | .transpGlue h0 h1 h2 h3 h4 h5 =>
    EqTm.transpGlue (toFull_ty h0) (toFull_ty h1) (toFull_ty h2) h3 h4 h5
  | .transpIPi h0 =>
    EqTm.transpIPi (toFull_ty h0)
  | .hcompIPi h0 =>
    EqTm.hcompIPi (toFull_ty h0)
  | .hcompPi h0 =>
    EqTm.hcompPi (toFull_ty h0)
  | .hcompSigma h0 =>
    EqTm.hcompSigma (toFull_ty h0)
  | .hcompPath h0 =>
    EqTm.hcompPath (toFull_ty h0)
  | .hcompGlue h0 h1 h2 =>
    EqTm.hcompGlue (toFull_ty h0) (toFull_ty h1) (toFull_ty h2)
  | .hcompU h0 =>
    EqTm.hcompU (toFull_ty h0)
  | .glueFace h0 h1 =>
    EqTm.glueFace h0 (toFull_ty h1)
  | .glueElFace h0 h1 =>
    EqTm.glueElFace h0 (toFull_ty h1)
  | .unglueFace h0 h1 h2 h3 =>
    EqTm.unglueFace h0 (toFull_ty h1) (toFull_ty h2) (toFull_ty h3)
  | .glueBeta h0 h1 =>
    EqTm.glueBeta (toFull_ty h0) (toFull_ty h1)
  | .glueEta h0 =>
    EqTm.glueEta (toFull_ty h0)
  | .data h0 h1 h2 h3 =>
    EqTm.data h0 (toFull_ty h1) (toFull_ty h2) (toFull_eqtele h3)
  | .con h0 h1 h2 h3 h4 h5 h6 h7 =>
    EqTm.con h0 h1 (toFull_ty h2) (toFull_ty h3) (toFull_eqtele h4) (toFull_eqtele h5) h6 h7
  | .elim h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 =>
    EqTm.elim h0 (toFull_ty h1) (toFull_ty h2) (toFull_eqtele h3) (toFull_eq h4) h5 h6 h7
        (fun c C b b' a1 a2 a3 => toFull_eq (h8 c C b b' a1 a2 a3)) (toFull_eq h9)
  | .conBnd h0 h1 h2 h3 h4 h5 h6 =>
    EqTm.conBnd h0 h1 h2 h3 h4 h5 (toFull_ty h6)
  | .elimCon h0 h1 h2 h3 h4 h5 h6 h7 =>
    EqTm.elimCon h0 h1 h2 h3 h4 h5 (toFull_tele h6) (toFull_ty h7)
  | .elimHcomp h0 h1 h2 =>
    EqTm.elimHcomp h0 (toFull_ty h1) (toFull_ty h2)
  | .transpData0 h0 h1 h2 =>
    EqTm.transpData0 h0 h1 (toFull_ty h2)
  | .transpCon h0 h1 h2 h3 h4 h5 h6 =>
    EqTm.transpCon h0 h1 h2 h3 h4 (toFull_tele h5) (toFull_ty h6)
  | .transpHcomp h0 h1 h2 h3 =>
    EqTm.transpHcomp h0 h1 (toFull_ty h2) (toFull_ty h3)
end

end KubusCore.Meta
