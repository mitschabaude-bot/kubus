import Model.Rules.Stubs

/-!
# Soundness and consistency

`sound_ty`/`sound_eq`: every derivation of the spec is valid in the model (by mutual induction
on derivations, dispatching to one lemma per rule), given a semantically valid signature.
-/

set_option autoImplicit false

namespace Model

open KubusCore KubusCore.Tm

mutual

theorem sound_wf {S : Sig} (hS : SigOK S) {Ψ : ℕ} {Φ : I} {Γ : Ctx} : Wf S Ψ Φ Γ → SemWf S Ψ Φ Γ
  | .nil h0 => sem_Wf_nil h0
  | .cons h0 => sem_Wf_cons (sound_ty hS h0)

theorem sound_ty {S : Sig} (hS : SigOK S) {Ψ : ℕ} {Φ : I} {Γ : Ctx} {t A : Tm} : HasTy S Ψ Φ Γ t A → SemTy S Ψ Φ Γ t A
  | .var h0 h1 => sem_HasTy_var (sound_wf hS h0) h1
  | .conv h0 h1 => sem_HasTy_conv (sound_ty hS h0) (sound_eq hS h1)
  | .restrict h0 h1 h2 => sem_HasTy_restrict h0 h1 (sound_ty hS h2)
  | .const h0 h1 => sem_HasTy_const hS (sound_wf hS h0) h1
  | .wk h0 h1 => sem_HasTy_wk (sound_ty hS h0) (sound_ty hS h1)
  | .dwk h0 => sem_HasTy_dwk (sound_ty hS h0)
  | .subst h0 h1 => sem_HasTy_subst (sound_ty hS h0) (sound_ty hS h1)
  | .dsubst h0 h1 => sem_HasTy_dsubst (sound_ty hS h0) h1
  | .eqL h0 => sem_HasTy_eqL (sound_eq hS h0)
  | .eqR h0 => sem_HasTy_eqR (sound_eq hS h0)
  | .piDom h0 => sem_HasTy_piDom (sound_ty hS h0)
  | .piCod h0 => sem_HasTy_piCod (sound_ty hS h0)
  | .sigmaDom h0 => sem_HasTy_sigmaDom (sound_ty hS h0)
  | .sigmaCod h0 => sem_HasTy_sigmaCod (sound_ty hS h0)
  | .pathLine h0 => sem_HasTy_pathLine (sound_ty hS h0)
  | .pathLeft h0 => sem_HasTy_pathLeft (sound_ty hS h0)
  | .pathRight h0 => sem_HasTy_pathRight (sound_ty hS h0)
  | .glueFib h0 => sem_HasTy_glueFib (sound_ty hS h0)
  | .univ h0 h1 => sem_HasTy_univ h0 (sound_wf hS h1)
  | .cumul h0 h1 => sem_HasTy_cumul h0 (sound_ty hS h1)
  | .pi h0 h1 => sem_HasTy_pi (sound_ty hS h0) (sound_ty hS h1)
  | .lam h0 h1 => sem_HasTy_lam (sound_ty hS h0) (sound_ty hS h1)
  | .app h0 h1 => sem_HasTy_app (sound_ty hS h0) (sound_ty hS h1)
  | .sigma h0 h1 => sem_HasTy_sigma (sound_ty hS h0) (sound_ty hS h1)
  | .pair h0 h1 h2 => sem_HasTy_pair (sound_ty hS h0) (sound_ty hS h1) (sound_ty hS h2)
  | .fst h0 => sem_HasTy_fst (sound_ty hS h0)
  | .snd h0 => sem_HasTy_snd (sound_ty hS h0)
  | .path h0 h1 h2 => sem_HasTy_path (sound_ty hS h0) (sound_ty hS h1) (sound_ty hS h2)
  | .plam h0 h1 h2 h3 => sem_HasTy_plam (sound_ty hS h0) (sound_ty hS h1) (sound_eq hS h2) (sound_eq hS h3)
  | .papp h0 h1 => sem_HasTy_papp (sound_ty hS h0) h1
  | .ipi h0 => sem_HasTy_ipi (sound_ty hS h0)
  | .ilam h0 h1 => sem_HasTy_ilam (sound_ty hS h0) (sound_ty hS h1)
  | .iapp h0 h1 => sem_HasTy_iapp (sound_ty hS h0) h1
  | .ipiLine h0 => sem_HasTy_ipiLine (sound_ty hS h0)
  | .split h0 h1 h2 h3 h4 h5 h6 => sem_HasTy_split h0 h1 h2 (sound_ty hS h3) (sound_ty hS h4) (sound_ty hS h5) (sound_eq hS h6)
  | .abort h0 h1 => sem_HasTy_abort h0 (sound_ty hS h1)
  | .transp h0 h1 h2 h3 => sem_HasTy_transp (sound_ty hS h0) h1 (sound_eq hS h2) (sound_ty hS h3)
  | .hcomp h0 h1 h2 h3 h4 => sem_HasTy_hcomp (sound_ty hS h0) h1 (sound_ty hS h2) (sound_ty hS h3) (sound_eq hS h4)
  | .glue h0 h1 h2 h3 => sem_HasTy_glue (sound_ty hS h0) h1 (sound_ty hS h2) (sound_ty hS h3)
  | .glueEl h0 h1 h2 h3 => sem_HasTy_glueEl (sound_ty hS h0) (sound_ty hS h1) (sound_ty hS h2) (sound_eq hS h3)
  | .unglue h0 h1 h2 h3 => sem_HasTy_unglue (sound_ty hS h0) (sound_ty hS h1) (sound_ty hS h2) (sound_ty hS h3)
  | .data h0 h1 h2 => sem_HasTy_data hS h0 h1 (sound_tele hS h2)
  | .con h0 h1 h2 h3 h4 h5 => sem_HasTy_con hS h0 h1 (sound_ty hS h2) (sound_tele hS h3) h4 h5
  | .elim h0 h1 h2 h3 h4 h5 h6 h7 => sem_HasTy_elim hS h0 (sound_ty hS h1) (sound_ty hS h2) h3 h4
      (fun c C b e1 e2 => sound_ty hS (h5 c C b e1 e2)) (fun c C b k ψ e e1 e2 e3 => sound_eq hS (h6 c C b k ψ e e1 e2 e3))
      (sound_ty hS h7)

theorem sound_tele {S : Sig} (hS : SigOK S) {Ψ : ℕ} {Φ : I} {Γ : Ctx} {as : Tm} {Δ prev : List Tm} :
    HasTele S Ψ Φ Γ as Δ prev → SemTele S Ψ Φ Γ as Δ prev
  | .nil h0 => sem_HasTele_nil (sound_wf hS h0)
  | .cons h0 h1 => sem_HasTele_cons (sound_ty hS h0) (sound_tele hS h1)

theorem sound_eqtele {S : Sig} (hS : SigOK S) {Ψ : ℕ} {Φ : I} {Γ : Ctx} {as as' : Tm} {Δ prev : List Tm} :
    EqTele S Ψ Φ Γ as as' Δ prev → SemEqTele S Ψ Φ Γ as as' Δ prev
  | .nil h0 => sem_EqTele_nil (sound_wf hS h0)
  | .cons h0 h1 => sem_EqTele_cons (sound_eq hS h0) (sound_eqtele hS h1)

theorem sound_eq {S : Sig} (hS : SigOK S) {Ψ : ℕ} {Φ : I} {Γ : Ctx} {t u A : Tm} : EqTm S Ψ Φ Γ t u A → SemEq S Ψ Φ Γ t u A
  | .refl h0 => sem_EqTm_refl (sound_ty hS h0)
  | .symm h0 => sem_EqTm_symm (sound_eq hS h0)
  | .trans h0 h1 => sem_EqTm_trans (sound_eq hS h0) (sound_eq hS h1)
  | .conv h0 h1 => sem_EqTm_conv (sound_eq hS h0) (sound_eq hS h1)
  | .restrict h0 h1 h2 => sem_EqTm_restrict h0 h1 (sound_eq hS h2)
  | .cumul h0 h1 => sem_EqTm_cumul h0 (sound_eq hS h1)
  | .wk h0 h1 => sem_EqTm_wk (sound_ty hS h0) (sound_eq hS h1)
  | .dwk h0 => sem_EqTm_dwk (sound_eq hS h0)
  | .subst h0 h1 => sem_EqTm_subst (sound_eq hS h0) (sound_eq hS h1)
  | .dsubst h0 h1 => sem_EqTm_dsubst (sound_eq hS h0) h1
  | .delta h0 h1 => sem_EqTm_delta hS (sound_ty hS h0) h1
  | .absurd h0 h1 h2 => sem_EqTm_absurd h0 (sound_ty hS h1) (sound_ty hS h2)
  | .local h0 h1 h2 h3 h4 h5 h6 => sem_EqTm_local h0 h1 h2 (sound_ty hS h3) (sound_ty hS h4) (sound_eq hS h5) (sound_eq hS h6)
  | .face h0 h1 h2 => sem_EqTm_face h0 h1 (sound_ty hS h2)
  | .pi h0 h1 => sem_EqTm_pi (sound_eq hS h0) (sound_eq hS h1)
  | .lam h0 h1 => sem_EqTm_lam (sound_ty hS h0) (sound_eq hS h1)
  | .app h0 h1 => sem_EqTm_app (sound_eq hS h0) (sound_eq hS h1)
  | .sigma h0 h1 => sem_EqTm_sigma (sound_eq hS h0) (sound_eq hS h1)
  | .pair h0 h1 h2 => sem_EqTm_pair (sound_ty hS h0) (sound_eq hS h1) (sound_eq hS h2)
  | .fst h0 => sem_EqTm_fst (sound_eq hS h0)
  | .snd h0 => sem_EqTm_snd (sound_eq hS h0)
  | .path h0 h1 h2 => sem_EqTm_path (sound_eq hS h0) (sound_eq hS h1) (sound_eq hS h2)
  | .plam h0 h1 h2 h3 => sem_EqTm_plam (sound_ty hS h0) (sound_ty hS h1) (sound_ty hS h2) (sound_eq hS h3)
  | .papp h0 h1 h2 h3 => sem_EqTm_papp (sound_eq hS h0) h1 h2 h3
  | .split h0 h1 h2 h3 => sem_EqTm_split (sound_ty hS h0) (sound_ty hS h1) (sound_eq hS h2) (sound_eq hS h3)
  | .transp h0 h1 h2 h3 h4 h5 => sem_EqTm_transp (sound_ty hS h0) (sound_ty hS h1) (sound_eq hS h2) h3 h4 (sound_eq hS h5)
  | .hcomp h0 h1 h2 h3 h4 h5 h6 => sem_EqTm_hcomp (sound_ty hS h0) (sound_ty hS h1) (sound_eq hS h2) h3 h4 (sound_eq hS h5) (sound_eq hS h6)
  | .glue h0 h1 h2 h3 h4 h5 h6 => sem_EqTm_glue (sound_ty hS h0) (sound_ty hS h1) (sound_eq hS h2) h3 h4 (sound_eq hS h5) (sound_eq hS h6)
  | .glueEl h0 h1 h2 h3 h4 h5 => sem_EqTm_glueEl (sound_ty hS h0) (sound_ty hS h1) h2 h3 (sound_eq hS h4) (sound_eq hS h5)
  | .unglue h0 h1 h2 h3 h4 => sem_EqTm_unglue (sound_ty hS h0) (sound_ty hS h1) h2 h3 (sound_eq hS h4)
  | .ipi h0 => sem_EqTm_ipi (sound_eq hS h0)
  | .ilam h0 h1 => sem_EqTm_ilam (sound_ty hS h0) (sound_eq hS h1)
  | .iapp h0 h1 h2 h3 => sem_EqTm_iapp (sound_eq hS h0) h1 h2 h3
  | .piBeta h0 => sem_EqTm_piBeta (sound_ty hS h0)
  | .piEta h0 => sem_EqTm_piEta (sound_ty hS h0)
  | .fstBeta h0 => sem_EqTm_fstBeta (sound_ty hS h0)
  | .sndBeta h0 => sem_EqTm_sndBeta (sound_ty hS h0)
  | .sigmaEta h0 => sem_EqTm_sigmaEta (sound_ty hS h0)
  | .pathBeta h0 => sem_EqTm_pathBeta (sound_ty hS h0)
  | .pathEta h0 => sem_EqTm_pathEta (sound_ty hS h0)
  | .ipiEta h0 => sem_EqTm_ipiEta (sound_ty hS h0)
  | .pathZero h0 => sem_EqTm_pathZero (sound_ty hS h0)
  | .pathOne h0 => sem_EqTm_pathOne (sound_ty hS h0)
  | .splitL h0 h1 => sem_EqTm_splitL h0 (sound_ty hS h1)
  | .splitR h0 h1 => sem_EqTm_splitR h0 (sound_ty hS h1)
  | .transpFace h0 h1 => sem_EqTm_transpFace h0 (sound_ty hS h1)
  | .hcompFace h0 h1 => sem_EqTm_hcompFace h0 (sound_ty hS h1)
  | .transpU h0 => sem_EqTm_transpU (sound_ty hS h0)
  | .transpPi h0 => sem_EqTm_transpPi (sound_ty hS h0)
  | .transpSigma h0 => sem_EqTm_transpSigma (sound_ty hS h0)
  | .transpPath h0 => sem_EqTm_transpPath (sound_ty hS h0)
  | .transpGlue h0 h1 h2 => sem_EqTm_transpGlue (sound_ty hS h0) (sound_ty hS h1) (sound_ty hS h2)
  | .transpIPi h0 => sem_EqTm_transpIPi (sound_ty hS h0)
  | .hcompIPi h0 => sem_EqTm_hcompIPi (sound_ty hS h0)
  | .hcompPi h0 => sem_EqTm_hcompPi (sound_ty hS h0)
  | .hcompSigma h0 => sem_EqTm_hcompSigma (sound_ty hS h0)
  | .hcompPath h0 => sem_EqTm_hcompPath (sound_ty hS h0)
  | .hcompGlue h0 h1 h2 => sem_EqTm_hcompGlue (sound_ty hS h0) (sound_ty hS h1) (sound_ty hS h2)
  | .hcompU h0 => sem_EqTm_hcompU (sound_ty hS h0)
  | .glueFace h0 h1 => sem_EqTm_glueFace h0 (sound_ty hS h1)
  | .glueElFace h0 h1 => sem_EqTm_glueElFace h0 (sound_ty hS h1)
  | .unglueFace h0 h1 h2 h3 => sem_EqTm_unglueFace h0 (sound_ty hS h1) (sound_ty hS h2) (sound_ty hS h3)
  | .glueBeta h0 => sem_EqTm_glueBeta (sound_ty hS h0)
  | .glueEta h0 => sem_EqTm_glueEta (sound_ty hS h0)
  | .data h0 h1 h2 h3 => sem_EqTm_data hS h0 (sound_ty hS h1) (sound_ty hS h2) (sound_eqtele hS h3)
  | .con h0 h1 h2 h3 h4 h5 h6 h7 => sem_EqTm_con hS h0 h1 (sound_ty hS h2) (sound_ty hS h3)
      (sound_eqtele hS h4) (sound_eqtele hS h5) h6 h7
  | .elim h0 h1 h2 h3 h4 h5 h6 h7 => sem_EqTm_elim hS h0 (sound_ty hS h1) (sound_ty hS h2) (sound_eqtele hS h3)
      (sound_eq hS h4) h5 (fun c C b b' e1 e2 e3 => sound_eq hS (h6 c C b b' e1 e2 e3)) (sound_eq hS h7)
  | .conBnd h0 h1 h2 h3 h4 => sem_EqTm_conBnd hS h0 h1 h2 h3 (sound_ty hS h4)
  | .elimCon h0 h1 h2 h3 => sem_EqTm_elimCon hS h0 h1 h2 (sound_ty hS h3)
  | .elimHcomp hd h0 => sem_EqTm_elimHcomp hS hd (sound_ty hS h0)
  | .transpData0 h0 h1 h2 => sem_EqTm_transpData0 hS h0 h1 (sound_ty hS h2)
  | .transpCon h0 h1 h2 h3 => sem_EqTm_transpCon hS h0 h1 h2 (sound_ty hS h3)
  | .transpHcomp h0 h1 h2 => sem_EqTm_transpHcomp hS h0 h1 (sound_ty hS h2)

end


end Model

namespace Model

open KubusCore

theorem take_take_eq {S : Sig} {k j : ℕ} (hj : j ≤ k) : (S.take k).take j = S.take j := by
  rw [List.take_take, Nat.min_eq_left hj]

/-- A well-formed signature is semantically valid. -/
theorem sigOK_of_wfSig : ∀ (n : ℕ) (S : Sig), S.length = n → WfSig S → SigOK S := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro S hn hS
    refine ⟨fun k t A hk => ?_, fun k D hk => sorry⟩
    have hklt : k < S.length := (List.getElem?_eq_some_iff.1 hk).1
    have hwf := hS.1 k t A hk
    have htake : WfSig (S.take k) := by
      refine ⟨fun j t' A' hj => ?_, fun j D' hj => ?_⟩
      · have hjk : j < k := by
          have := (List.getElem?_eq_some_iff.1 hj).1
          simpa [List.length_take, hklt.le] using this
        rw [List.getElem?_take_of_lt hjk] at hj
        have := hS.1 j t' A' hj
        rwa [take_take_eq hjk.le]
      · have hjk : j < k := by
          have := (List.getElem?_eq_some_iff.1 hj).1
          simpa [List.length_take, hklt.le] using this
        rw [List.getElem?_take_of_lt hjk] at hj
        have := hS.2 j D' hj
        rwa [take_take_eq (by omega)]
    have hok : SigOK (S.take k) := ih _ (by rw [← hn, List.length_take]; omega) _ rfl htake
    exact ⟨hwf.1, hwf.2.1, sound_ty hok hwf.2.2.2⟩

end Model
