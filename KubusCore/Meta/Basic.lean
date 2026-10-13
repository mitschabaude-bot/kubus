import KubusCore.Meta.Minimal

/-!
# Metatheory: basic facts about the minimal judgments
-/

namespace KubusCore.Meta

open Tm

variable {S : Sig}

theorem Wf0.restrict {Ψ Φ Φ' Γ} (h : Wf0 S Ψ Φ Γ) (hs : Φ'.Scoped Ψ) (he : I.Entails Φ' Φ) :
    Wf0 S Ψ Φ' Γ := by
  cases h with
  | nil _ => exact Wf0.nil hs
  | cons hA => exact Wf0.cons (HasTy0.restrict hs he hA)

/-! ## Every judgment has a well-formed context -/

mutual
theorem wf_of_ty {Ψ Φ Γ t A} : HasTy0 S Ψ Φ Γ t A → Wf0 S Ψ Φ Γ
  | .var h0 _ => h0
  | .conv h0 _ => wf_of_ty h0
  | .restrict h0 h1 h2 => (wf_of_ty h2).restrict h0 h1
  | .const h0 _ => h0
  | .univ _ h1 => h1
  | .cumul _ h1 => wf_of_ty h1
  | .pi h0 _ => wf_of_ty h0
  | .lam h0 _ => wf_of_ty h0
  | .app h0 _ => wf_of_ty h0
  | .sigma h0 _ => wf_of_ty h0
  | .pair h0 _ _ => wf_of_ty h0
  | .fst h0 => wf_of_ty h0
  | .snd h0 => wf_of_ty h0
  | .path _ h1 _ => wf_of_ty h1
  | .plam h0 _ _ _ => wf_of_ty h0
  | .papp h0 _ => wf_of_ty h0
  | .ipi h0 _ => h0
  | .ilam h0 _ => wf_of_ty h0
  | .iapp h0 _ => wf_of_ty h0
  | .split _ _ _ h3 _ _ _ => wf_of_ty h3
  | .abort _ h1 => wf_of_ty h1
  | .transp _ _ _ h3 => wf_of_ty h3
  | .hcomp h0 _ _ _ _ => wf_of_ty h0
  | .glue h0 _ _ _ => wf_of_ty h0
  | .glueEl h0 _ _ _ _ => wf_of_ty h0
  | .unglue h0 _ _ _ => wf_of_ty h0
  | .data _ _ h2 => wf_of_tele h2
  | .con _ _ _ h3 _ _ _ _ => wf_of_ty h3
  | .elim _ _ h2 _ _ _ _ _ _ _ => wf_of_ty h2

theorem wf_of_tele {Ψ Φ Γ ts Δ prev} : HasTele0 S Ψ Φ Γ ts Δ prev → Wf0 S Ψ Φ Γ
  | .nil h0 => h0
  | .cons h0 _ => wf_of_ty h0

theorem wf_of_eqtele {Ψ Φ Γ ts ts' Δ prev} : EqTele0 S Ψ Φ Γ ts ts' Δ prev → Wf0 S Ψ Φ Γ
  | .nil h0 => h0
  | .cons h0 _ => wf_of_eq h0
  | .dataInj _ h1 _ _ => wf_of_tele h1

theorem wf_of_eq {Ψ Φ Γ t u A} : EqTm0 S Ψ Φ Γ t u A → Wf0 S Ψ Φ Γ
  | .refl h0 => wf_of_ty h0
  | .symm h0 => wf_of_eq h0
  | .trans h0 _ => wf_of_eq h0
  | .conv h0 _ => wf_of_eq h0
  | .restrict h0 h1 h2 => (wf_of_eq h2).restrict h0 h1
  | .cumul _ h1 => wf_of_eq h1
  | .delta h0 _ => wf_of_ty h0
  | .absurd _ h1 _ => wf_of_ty h1
  | .local _ _ _ h3 _ _ _ => wf_of_ty h3
  | .face _ _ h2 _ => wf_of_ty h2
  | .faceU _ _ h2 => wf_of_ty h2
  | .pi h0 _ => wf_of_eq h0
  | .lam h0 _ => wf_of_ty h0
  | .app h0 _ => wf_of_eq h0
  | .sigma h0 _ => wf_of_eq h0
  | .pair h0 _ _ => wf_of_ty h0
  | .fst h0 => wf_of_eq h0
  | .snd h0 => wf_of_eq h0
  | .path _ h1 _ => wf_of_eq h1
  | .plam h0 _ _ _ => wf_of_ty h0
  | .papp h0 _ _ _ => wf_of_eq h0
  | .split h0 _ _ _ => wf_of_ty h0
  | .transp h0 _ _ _ _ _ => wf_of_ty h0
  | .hcomp h0 _ _ _ _ _ _ => wf_of_ty h0
  | .glue h0 _ _ _ _ _ _ => wf_of_ty h0
  | .glueEl h0 _ _ _ _ _ _ => wf_of_ty h0
  | .unglue h0 _ _ _ _ _ => wf_of_ty h0
  | .ipi h0 _ => h0
  | .ilam h0 _ => wf_of_ty h0
  | .iapp h0 _ _ _ => wf_of_eq h0
  | .piBeta h0 => wf_of_ty h0
  | .piEta h0 => wf_of_ty h0
  | .fstBeta h0 => wf_of_ty h0
  | .sndBeta h0 => wf_of_ty h0
  | .sigmaEta h0 => wf_of_ty h0
  | .pathBeta h0 => wf_of_ty h0
  | .pathEta h0 => wf_of_ty h0
  | .ipiEta h0 => wf_of_ty h0
  | .pathZero h0 => wf_of_ty h0
  | .pathOne h0 => wf_of_ty h0
  | .splitL _ h1 => wf_of_ty h1
  | .splitR _ h1 => wf_of_ty h1
  | .transpFace _ h1 => wf_of_ty h1
  | .hcompFace _ h1 => wf_of_ty h1
  | .transpU h0 => wf_of_ty h0
  | .transpPi h0 => wf_of_ty h0
  | .transpSigma h0 => wf_of_ty h0
  | .transpPath h0 => wf_of_ty h0
  | .transpGlue h0 _ _ _ _ => wf_of_ty h0
  | .transpIPi h0 => wf_of_ty h0
  | .hcompIPi h0 => wf_of_ty h0
  | .hcompPi h0 => wf_of_ty h0
  | .hcompSigma h0 => wf_of_ty h0
  | .hcompPath h0 => wf_of_ty h0
  | .hcompGlue h0 _ _ => wf_of_ty h0
  | .hcompU h0 => wf_of_ty h0
  | .glueFace _ h1 => wf_of_ty h1
  | .glueElFace _ h1 => wf_of_ty h1
  | .unglueFace _ h1 _ _ => wf_of_ty h1
  | .glueBeta h0 _ => wf_of_ty h0
  | .noConf _ h1 _ _ => wf_of_eq h1
  | .piInjDom h0 => wf_of_eq h0
  | .piInjCod h0 _ => wf_of_eq h0
  | .sigmaInjDom h0 => wf_of_eq h0
  | .sigmaInjCod h0 _ => wf_of_eq h0
  | .pathInjLine h0 _ => wf_of_eq h0
  | .pathInjLeft h0 => wf_of_eq h0
  | .pathInjRight h0 => wf_of_eq h0
  | .ipiInj h0 _ => wf_of_eq h0
  | .glueEta h0 => wf_of_ty h0
  | .data _ h1 _ _ => wf_of_ty h1
  | .con _ _ h2 _ _ _ _ _ => wf_of_ty h2
  | .elim _ h1 _ _ _ _ _ _ _ _ => wf_of_ty h1
  | .conBnd _ _ _ _ _ _ h6 => wf_of_ty h6
  | .elimCon _ _ _ _ _ _ _ h7 => wf_of_ty h7
  | .elimHcomp _ _ h2 => wf_of_ty h2
  | .transpData0 _ _ h2 => wf_of_ty h2
  | .transpCon _ _ _ _ _ _ h6 => wf_of_ty h6
  | .transpHcomp _ _ _ h3 => wf_of_ty h3
end

end KubusCore.Meta
