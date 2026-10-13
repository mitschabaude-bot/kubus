import KubusCore.Meta.Main

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

theorem sigwk_wf (hpre : ∀ (k : Nat) (e : Entry), S'[k]? = some e → S[k]? = some e) {Ψ Φ Γ} : Wf0 S' Ψ Φ Γ → Wf0 S Ψ Φ Γ
  | .nil h0 => Wf0.nil h0
  | .cons h0 => Wf0.cons (sigwk_ty hpre h0)

theorem sigwk_ty (hpre : ∀ (k : Nat) (e : Entry), S'[k]? = some e → S[k]? = some e) {Ψ Φ Γ t A} : HasTy0 S' Ψ Φ Γ t A → HasTy0 S Ψ Φ Γ t A
  | .var h0 h1 => HasTy0.var (sigwk_wf hpre h0) h1
  | .conv h0 h1 => HasTy0.conv (sigwk_ty hpre h0) (sigwk_eq hpre h1)
  | .restrict h0 h1 h2 => HasTy0.restrict h0 h1 (sigwk_ty hpre h2)
  | .const h0 h1 => HasTy0.const (sigwk_wf hpre h0) (hpre _ _ h1)
  | .univ h0 h1 => HasTy0.univ h0 (sigwk_wf hpre h1)
  | .cumul h0 h1 => HasTy0.cumul h0 (sigwk_ty hpre h1)
  | .pi h0 h1 => HasTy0.pi (sigwk_ty hpre h0) (sigwk_ty hpre h1)
  | .lam h0 h1 => HasTy0.lam (sigwk_ty hpre h0) (sigwk_ty hpre h1)
  | .app h0 h1 => HasTy0.app (sigwk_ty hpre h0) (sigwk_ty hpre h1)
  | .sigma h0 h1 => HasTy0.sigma (sigwk_ty hpre h0) (sigwk_ty hpre h1)
  | .pair h0 h1 h2 => HasTy0.pair (sigwk_ty hpre h0) (sigwk_ty hpre h1) (sigwk_ty hpre h2)
  | .fst h0 => HasTy0.fst (sigwk_ty hpre h0)
  | .snd h0 => HasTy0.snd (sigwk_ty hpre h0)
  | .path h0 h1 h2 => HasTy0.path (sigwk_ty hpre h0) (sigwk_ty hpre h1) (sigwk_ty hpre h2)
  | .plam h0 h1 h2 h3 => HasTy0.plam (sigwk_ty hpre h0) (sigwk_ty hpre h1) (sigwk_eq hpre h2) (sigwk_eq hpre h3)
  | .papp h0 h1 => HasTy0.papp (sigwk_ty hpre h0) h1
  | .ipi h0 h1 => HasTy0.ipi (sigwk_wf hpre h0) (sigwk_ty hpre h1)
  | .ilam h0 h1 => HasTy0.ilam (sigwk_ty hpre h0) (sigwk_ty hpre h1)
  | .iapp h0 h1 => HasTy0.iapp (sigwk_ty hpre h0) h1
  | .split h0 h1 h2 h3 h4 h5 h6 => HasTy0.split h0 h1 h2 (sigwk_ty hpre h3) (sigwk_ty hpre h4) (sigwk_ty hpre h5) (sigwk_eq hpre h6)
  | .abort h0 h1 => HasTy0.abort h0 (sigwk_ty hpre h1)
  | .transp h0 h1 h2 h3 => HasTy0.transp (sigwk_ty hpre h0) h1 (sigwk_eq hpre h2) (sigwk_ty hpre h3)
  | .hcomp h0 h1 h2 h3 h4 => HasTy0.hcomp (sigwk_ty hpre h0) h1 (sigwk_ty hpre h2) (sigwk_ty hpre h3) (sigwk_eq hpre h4)
  | .glue h0 h1 h2 h3 => HasTy0.glue (sigwk_ty hpre h0) h1 (sigwk_ty hpre h2) (sigwk_ty hpre h3)
  | .glueEl h0 h1 h2 h3 h4 => HasTy0.glueEl (sigwk_ty hpre h0) (sigwk_ty hpre h1) (sigwk_ty hpre h2) (sigwk_ty hpre h3) (sigwk_eq hpre h4)
  | .unglue h0 h1 h2 h3 => HasTy0.unglue (sigwk_ty hpre h0) (sigwk_ty hpre h1) (sigwk_ty hpre h2) (sigwk_ty hpre h3)
  | .data h0 h1 h2 => HasTy0.data (hpre _ _ h0) h1 (sigwk_tele hpre h2)
  | .con h0 h1 h2 h3 h4 h5 h6 h7 => HasTy0.con (hpre _ _ h0) h1 h2 (sigwk_ty hpre h3) (sigwk_tele hpre h4) (sigwk_tele hpre h5) h6 h7
  | .elim h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 => HasTy0.elim (hpre _ _ h0) h1 (sigwk_ty hpre h2) (sigwk_tele hpre h3) (sigwk_ty hpre h4) h5 h6 (fun c C b a0 a1 => sigwk_ty hpre (h7 c C b a0 a1)) (fun c C b k ψ e a0 a1 a2 => sigwk_eq hpre (h8 c C b k ψ e a0 a1 a2)) (sigwk_ty hpre h9)

theorem sigwk_tele (hpre : ∀ (k : Nat) (e : Entry), S'[k]? = some e → S[k]? = some e) {Ψ Φ Γ ts Δ prev} : HasTele0 S' Ψ Φ Γ ts Δ prev → HasTele0 S Ψ Φ Γ ts Δ prev
  | .nil h0 => HasTele0.nil (sigwk_wf hpre h0)
  | .cons h0 h1 => HasTele0.cons (sigwk_ty hpre h0) (sigwk_tele hpre h1)

theorem sigwk_eqtele (hpre : ∀ (k : Nat) (e : Entry), S'[k]? = some e → S[k]? = some e) {Ψ Φ Γ ts ts' Δ prev} : EqTele0 S' Ψ Φ Γ ts ts' Δ prev → EqTele0 S Ψ Φ Γ ts ts' Δ prev
  | .nil h0 => EqTele0.nil (sigwk_wf hpre h0)
  | .cons h0 h1 => EqTele0.cons (sigwk_eq hpre h0) (sigwk_eqtele hpre h1)

theorem sigwk_eq (hpre : ∀ (k : Nat) (e : Entry), S'[k]? = some e → S[k]? = some e) {Ψ Φ Γ t u A} : EqTm0 S' Ψ Φ Γ t u A → EqTm0 S Ψ Φ Γ t u A
  | .refl h0 => EqTm0.refl (sigwk_ty hpre h0)
  | .symm h0 => EqTm0.symm (sigwk_eq hpre h0)
  | .trans h0 h1 => EqTm0.trans (sigwk_eq hpre h0) (sigwk_eq hpre h1)
  | .conv h0 h1 => EqTm0.conv (sigwk_eq hpre h0) (sigwk_eq hpre h1)
  | .restrict h0 h1 h2 => EqTm0.restrict h0 h1 (sigwk_eq hpre h2)
  | .cumul h0 h1 => EqTm0.cumul h0 (sigwk_eq hpre h1)
  | .delta h0 h1 => EqTm0.delta (sigwk_ty hpre h0) (hpre _ _ h1)
  | .absurd h0 h1 h2 => EqTm0.absurd h0 (sigwk_ty hpre h1) (sigwk_ty hpre h2)
  | .local h0 h1 h2 h3 h4 h5 h6 => EqTm0.local h0 h1 h2 (sigwk_ty hpre h3) (sigwk_ty hpre h4) (sigwk_eq hpre h5) (sigwk_eq hpre h6)
  | .face h0 h1 h2 h3 => EqTm0.face h0 h1 (sigwk_ty hpre h2) (sigwk_ty hpre h3)
  | .faceU h0 h1 h2 => EqTm0.faceU h0 h1 (sigwk_ty hpre h2)
  | .pi h0 h1 => EqTm0.pi (sigwk_eq hpre h0) (sigwk_eq hpre h1)
  | .lam h0 h1 => EqTm0.lam (sigwk_ty hpre h0) (sigwk_eq hpre h1)
  | .app h0 h1 => EqTm0.app (sigwk_eq hpre h0) (sigwk_eq hpre h1)
  | .sigma h0 h1 => EqTm0.sigma (sigwk_eq hpre h0) (sigwk_eq hpre h1)
  | .pair h0 h1 h2 => EqTm0.pair (sigwk_ty hpre h0) (sigwk_eq hpre h1) (sigwk_eq hpre h2)
  | .fst h0 => EqTm0.fst (sigwk_eq hpre h0)
  | .snd h0 => EqTm0.snd (sigwk_eq hpre h0)
  | .path h0 h1 h2 => EqTm0.path (sigwk_eq hpre h0) (sigwk_eq hpre h1) (sigwk_eq hpre h2)
  | .plam h0 h1 h2 h3 => EqTm0.plam (sigwk_ty hpre h0) (sigwk_ty hpre h1) (sigwk_ty hpre h2) (sigwk_eq hpre h3)
  | .papp h0 h1 h2 h3 => EqTm0.papp (sigwk_eq hpre h0) h1 h2 h3
  | .split h0 h1 h2 h3 => EqTm0.split (sigwk_ty hpre h0) (sigwk_ty hpre h1) (sigwk_eq hpre h2) (sigwk_eq hpre h3)
  | .transp h0 h1 h2 h3 h4 h5 => EqTm0.transp (sigwk_ty hpre h0) (sigwk_ty hpre h1) (sigwk_eq hpre h2) h3 h4 (sigwk_eq hpre h5)
  | .hcomp h0 h1 h2 h3 h4 h5 h6 => EqTm0.hcomp (sigwk_ty hpre h0) (sigwk_ty hpre h1) (sigwk_eq hpre h2) h3 h4 (sigwk_eq hpre h5) (sigwk_eq hpre h6)
  | .glue h0 h1 h2 h3 h4 h5 h6 => EqTm0.glue (sigwk_ty hpre h0) (sigwk_ty hpre h1) (sigwk_eq hpre h2) h3 h4 (sigwk_eq hpre h5) (sigwk_eq hpre h6)
  | .glueEl h0 h1 h2 h3 h4 h5 h6 => EqTm0.glueEl (sigwk_ty hpre h0) (sigwk_ty hpre h1) h2 h3 (sigwk_eq hpre h4) (sigwk_eq hpre h5) (sigwk_eq hpre h6)
  | .unglue h0 h1 h2 h3 h4 h5 => EqTm0.unglue (sigwk_ty hpre h0) (sigwk_ty hpre h1) h2 h3 (sigwk_eq hpre h4) (sigwk_eq hpre h5)
  | .ipi h0 h1 => EqTm0.ipi (sigwk_wf hpre h0) (sigwk_eq hpre h1)
  | .ilam h0 h1 => EqTm0.ilam (sigwk_ty hpre h0) (sigwk_eq hpre h1)
  | .iapp h0 h1 h2 h3 => EqTm0.iapp (sigwk_eq hpre h0) h1 h2 h3
  | .piBeta h0 => EqTm0.piBeta (sigwk_ty hpre h0)
  | .piEta h0 => EqTm0.piEta (sigwk_ty hpre h0)
  | .fstBeta h0 => EqTm0.fstBeta (sigwk_ty hpre h0)
  | .sndBeta h0 => EqTm0.sndBeta (sigwk_ty hpre h0)
  | .sigmaEta h0 => EqTm0.sigmaEta (sigwk_ty hpre h0)
  | .pathBeta h0 => EqTm0.pathBeta (sigwk_ty hpre h0)
  | .pathEta h0 => EqTm0.pathEta (sigwk_ty hpre h0)
  | .ipiEta h0 => EqTm0.ipiEta (sigwk_ty hpre h0)
  | .pathZero h0 => EqTm0.pathZero (sigwk_ty hpre h0)
  | .pathOne h0 => EqTm0.pathOne (sigwk_ty hpre h0)
  | .splitL h0 h1 => EqTm0.splitL h0 (sigwk_ty hpre h1)
  | .splitR h0 h1 => EqTm0.splitR h0 (sigwk_ty hpre h1)
  | .transpFace h0 h1 => EqTm0.transpFace h0 (sigwk_ty hpre h1)
  | .hcompFace h0 h1 => EqTm0.hcompFace h0 (sigwk_ty hpre h1)
  | .transpU h0 => EqTm0.transpU (sigwk_ty hpre h0)
  | .transpPi h0 => EqTm0.transpPi (sigwk_ty hpre h0)
  | .transpSigma h0 => EqTm0.transpSigma (sigwk_ty hpre h0)
  | .transpPath h0 => EqTm0.transpPath (sigwk_ty hpre h0)
  | .transpGlue h0 h1 h2 h3 h4 => EqTm0.transpGlue (sigwk_ty hpre h0) (sigwk_ty hpre h1) (sigwk_ty hpre h2) h3 h4
  | .transpIPi h0 => EqTm0.transpIPi (sigwk_ty hpre h0)
  | .hcompIPi h0 => EqTm0.hcompIPi (sigwk_ty hpre h0)
  | .hcompPi h0 => EqTm0.hcompPi (sigwk_ty hpre h0)
  | .hcompSigma h0 => EqTm0.hcompSigma (sigwk_ty hpre h0)
  | .hcompPath h0 => EqTm0.hcompPath (sigwk_ty hpre h0)
  | .hcompGlue h0 h1 h2 => EqTm0.hcompGlue (sigwk_ty hpre h0) (sigwk_ty hpre h1) (sigwk_ty hpre h2)
  | .hcompU h0 => EqTm0.hcompU (sigwk_ty hpre h0)
  | .glueFace h0 h1 => EqTm0.glueFace h0 (sigwk_ty hpre h1)
  | .glueElFace h0 h1 => EqTm0.glueElFace h0 (sigwk_ty hpre h1)
  | .unglueFace h0 h1 h2 h3 => EqTm0.unglueFace h0 (sigwk_ty hpre h1) (sigwk_ty hpre h2) (sigwk_ty hpre h3)
  | .glueBeta h0 => EqTm0.glueBeta (sigwk_ty hpre h0)
  | .glueEta h0 => EqTm0.glueEta (sigwk_ty hpre h0)
  | .data h0 h1 h2 h3 => EqTm0.data (hpre _ _ h0) (sigwk_ty hpre h1) (sigwk_ty hpre h2) (sigwk_eqtele hpre h3)
  | .con h0 h1 h2 h3 h4 h5 h6 h7 => EqTm0.con (hpre _ _ h0) h1 (sigwk_ty hpre h2) (sigwk_ty hpre h3) (sigwk_eqtele hpre h4) (sigwk_eqtele hpre h5) h6 h7
  | .elim h0 h1 h2 h3 h4 h5 h6 h7 => EqTm0.elim (hpre _ _ h0) (sigwk_ty hpre h1) (sigwk_ty hpre h2) (sigwk_eqtele hpre h3) (sigwk_eq hpre h4) h5 (fun c C b b' a0 a1 a2 => sigwk_eq hpre (h6 c C b b' a0 a1 a2)) (sigwk_eq hpre h7)
  | .conBnd h0 h1 h2 h3 h4 h5 h6 => EqTm0.conBnd (hpre _ _ h0) h1 h2 h3 h4 h5 (sigwk_ty hpre h6)
  | .elimCon h0 h1 h2 h3 h4 h5 => EqTm0.elimCon (hpre _ _ h0) h1 h2 h3 h4 (sigwk_ty hpre h5)
  | .elimHcomp h0 h1 => EqTm0.elimHcomp (hpre _ _ h0) (sigwk_ty hpre h1)
  | .transpData0 h0 h1 h2 => EqTm0.transpData0 (hpre _ _ h0) h1 (sigwk_ty hpre h2)
  | .transpCon h0 h1 h2 h3 h4 h5 => EqTm0.transpCon (hpre _ _ h0) h1 h2 h3 h4 (sigwk_ty hpre h5)
  | .transpHcomp h0 h1 h2 => EqTm0.transpHcomp (hpre _ _ h0) h1 (sigwk_ty hpre h2)
end

end KubusCore.Meta

namespace KubusCore.Meta

theorem take_take_le {S : Sig} {k j : Nat} (hj : j ≤ k) : (S.take k).take j = S.take j := by
  rw [List.take_take, Nat.min_eq_left hj]

theorem getElem?_take_some {S : Sig} {k j : Nat} {e : Entry} (h : (S.take k)[j]? = some e) :
    j < k ∧ S[j]? = some e := by
  have hj : j < k := by
    have := (List.getElem?_eq_some_iff.1 h).1
    simp [List.length_take] at this; omega
  rw [List.getElem?_take_of_lt hj] at h
  exact ⟨hj, h⟩

theorem wfSig_take {S : Sig} (h : WfSig S) (k : Nat) : WfSig (S.take k) := by
  refine ⟨fun j t A hj => ?_, fun j D hj => ?_⟩
  · obtain ⟨hjk, hj⟩ := getElem?_take_some hj
    rw [take_take_le (Nat.le_of_lt hjk)]; exact h.1 j t A hj
  · obtain ⟨hjk, hj⟩ := getElem?_take_some hj
    rw [take_take_le (Nat.le_of_lt hjk)]; exact h.2 j D hj

/-- The definitions of a well-formed signature are typed in the minimal judgments, given
`ContractaTyped` for its prefixes. -/
theorem sigTyped0_of_wfSig : ∀ (n : Nat) (S : Sig), S.length = n → WfSig S →
    (∀ k, ContractaTyped (S.take k)) → SigTyped0 S := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro S hn hS hC k t A hk
    have hklt : k < S.length := (List.getElem?_eq_some_iff.1 hk).1
    have hwf := hS.1 k t A hk
    have hS' := wfSig_take hS k
    have hT' : SigTyped0 (S.take k) :=
      ih k (by rw [← hn]; exact hklt) (S.take k) (by simp [List.length_take]; omega) hS'
        (fun j => by rw [List.take_take]; exact hC _)
    have hpre : ∀ (j : Nat) (e : Entry), (S.take k)[j]? = some e → S[j]? = some e :=
      fun j e h => (getElem?_take_some h).2
    obtain ⟨l, hA⟩ := hwf.2.2.1
    exact ⟨⟨l, sigwk_ty hpre (spec_to_minimal hS' hT' (hC k) hA)⟩,
      sigwk_ty hpre (spec_to_minimal hS' hT' (hC k) hwf.2.2.2)⟩

/-- The spec's typing judgment adds nothing to the minimal one, for a well-formed signature
whose prefixes satisfy `ContractaTyped`. -/
theorem spec_to_minimal' {S : Sig} (hS : WfSig S) (hC : ∀ k, ContractaTyped (S.take k)) {Ψ Φ Γ t A}
    (h : HasTy S Ψ Φ Γ t A) : HasTy0 S Ψ Φ Γ t A :=
  spec_to_minimal hS (sigTyped0_of_wfSig _ S rfl hS hC) (by simpa using hC S.length) h

theorem spec_to_minimal_eq' {S : Sig} (hS : WfSig S) (hC : ∀ k, ContractaTyped (S.take k))
    {Ψ Φ Γ t u A} (h : EqTm S Ψ Φ Γ t u A) : EqTm0 S Ψ Φ Γ t u A :=
  spec_to_minimal_eq hS (sigTyped0_of_wfSig _ S rfl hS hC) (by simpa using hC S.length) h

end KubusCore.Meta
