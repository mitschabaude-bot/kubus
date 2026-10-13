import KubusCore.Meta.SubBranch

/-!
# Metatheory: substitution is admissible

`sub_ty`/`sub_eq`: the minimal judgments are closed under simultaneous substitution of term
variables and interval variables (`TySub`), and typing is functional in the substitution
(`FunP`: judgmentally equal term substitutions and interval substitutions that are equal in
the free De Morgan algebra give judgmentally equal results). The two are proven together, and
the face rule's case uses `face_lemma`. The signature must be closed (`SigClosed`).
-/

set_option maxHeartbeats 4000000

namespace KubusCore.Meta

open Tm

variable {S : Sig}

mutual

theorem sub_wf (hS : SigClosed S) {Ψ Φ Γ} : Wf0 S Ψ Φ Γ → CtxSub S Ψ Φ Γ
  | .nil _ => trivial
  | .cons h0 => ⟨(sub_ty hS h0).1, _, (sub_ty hS h0).2.1, (sub_ty hS h0).2.2,
      face_lemma (scoped_of_ty h0) (sub_ty hS h0).1 (sub_ty hS h0).2.1 (sub_ty hS h0).2.2 (Or.inl ⟨_, rfl⟩)⟩

theorem sub_ty (hS : SigClosed S) {Ψ Φ Γ t A} : HasTy0 S Ψ Φ Γ t A →
    CtxSub S Ψ Φ Γ ∧ SubP S Ψ Φ Γ t A ∧ FunP S Ψ Φ Γ t A
  | @HasTy0.var _ Ψ Φ Γ x A h0 h1 =>
    have hsub : SubP S Ψ Φ Γ (var x) A := fun {Ψ' Φ' Δ σ τ} hσ =>
      by simp only [Tm.subst]; exact hσ.look _ _ h1
    ⟨sub_wf hS h0, hsub, fun {Ψ' Φ' Δ σ1 τ1 σ2 τ2} k1 k2 kE =>
      kE.1 _ _ h1⟩
  | @HasTy0.conv _ Ψ Φ Γ t A B l h0 h1 =>
    have hsub : SubP S Ψ Φ Γ t B := fun {Ψ' Φ' Δ σ τ} hσ =>
      HasTy0.conv ((sub_ty hS h0).2.1 hσ) ((sub_eq hS h1).2 hσ)
    ⟨(sub_ty hS h0).1, hsub, fun {Ψ' Φ' Δ σ1 τ1 σ2 τ2} k1 k2 kE =>
      EqTm0.conv ((sub_ty hS h0).2.2 k1 k2 kE) ((sub_eq hS h1).2 k1)⟩
  | @HasTy0.restrict _ Ψ Φ Φ' Γ t A h0 h1 h2 =>
    have hsub : SubP S Ψ Φ' Γ t A := fun {Ψ' Φ' Δ σ τ} hσ =>
      (sub_ty hS h2).2.1 (hσ.restrictSrc h1)
    ⟨CtxSub.restrictSrc h1 (sub_ty hS h2).1, hsub, fun {Ψ' Φ' Δ σ1 τ1 σ2 τ2} k1 k2 kE =>
      (sub_ty hS h2).2.2 (k1.restrictSrc h1) (k2.restrictSrc h1) kE⟩
  | @HasTy0.const _ Ψ Φ Γ k t A h0 h1 =>
    have hsub : SubP S Ψ Φ Γ (const k) A := fun {Ψ' Φ' Δ σ τ} hσ =>
      by obtain ⟨_, hA⟩ := hS.defn _ _ _ h1; rw [closed_subst_id hA (fun _ h => absurd h (Nat.not_lt_zero _)) (fun _ h => absurd h (Nat.not_lt_zero _))]; exact HasTy0.const hσ.wf h1
    ⟨sub_wf hS h0, hsub, fun {Ψ' Φ' Δ σ1 τ1 σ2 τ2} k1 k2 kE =>
      EqTm0.refl (hsub k1)⟩
  | @HasTy0.univ _ Ψ Φ Γ l h0 h1 =>
    have hsub : SubP S Ψ Φ Γ (univ l) (univ (l + 1)) := fun {Ψ' Φ' Δ σ τ} hσ =>
      HasTy0.univ h0 hσ.wf
    ⟨sub_wf hS h1, hsub, fun {Ψ' Φ' Δ σ1 τ1 σ2 τ2} k1 k2 kE =>
      EqTm0.refl (hsub k1)⟩
  | @HasTy0.cumul _ Ψ Φ Γ A l h0 h1 =>
    have hsub : SubP S Ψ Φ Γ A (univ (l + 1)) := fun {Ψ' Φ' Δ σ τ} hσ =>
      HasTy0.cumul h0 ((sub_ty hS h1).2.1 hσ)
    ⟨(sub_ty hS h1).1, hsub, fun {Ψ' Φ' Δ σ1 τ1 σ2 τ2} k1 k2 kE =>
      EqTm0.cumul h0 ((sub_ty hS h1).2.2 k1 k2 kE)⟩
  | @HasTy0.pi _ Ψ Φ Γ A B l h0 h1 =>
    have hsub : SubP S Ψ Φ Γ (pi A B) (univ l) := fun {Ψ' Φ' Δ σ τ} hσ =>
      by simp only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil]; exact HasTy0.pi ((sub_ty hS h0).2.1 hσ) ((sub_ty hS h1).2.1 (hσ.upC hS (sub_ty hS h1).1))
    ⟨(sub_ty hS h0).1, hsub, fun {Ψ' Φ' Δ σ1 τ1 σ2 τ2} k1 k2 kE =>
      by obtain ⟨u1, u2, uE⟩ := TySub.up2 hS k1 k2 kE (sub_ty hS h1).1; exact EqTm0.pi ((sub_ty hS h0).2.2 k1 k2 kE) ((sub_ty hS h1).2.2 u1 u2 uE)⟩
  | @HasTy0.lam _ Ψ Φ Γ A B t l h0 h1 =>
    have hsub : SubP S Ψ Φ Γ (lam A t) (pi A B) := fun {Ψ' Φ' Δ σ τ} hσ =>
      by simp only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil]; exact HasTy0.lam (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil] using (sub_ty hS h0).2.1 hσ) ((sub_ty hS h1).2.1 (hσ.upC hS (sub_ty hS h1).1))
    ⟨(sub_ty hS h0).1, hsub, fun {Ψ' Φ' Δ σ1 τ1 σ2 τ2} k1 k2 kE =>
      by
      obtain ⟨u1, u2, uE⟩ := TySub.up2 hS k1 k2 kE (sub_ty hS h1).1
      obtain ⟨_, _, hA, _, _⟩ := (sub_ty hS h1).1
      exact lam_congr' hS (hA k1) ((sub_ty hS h0).2.1 k1) (HasTy0.conv (hsub k2) (EqTm0.symm ((sub_ty hS h0).2.2 k1 k2 kE))) ((sub_ty hS h1).2.2 u1 u2 uE)⟩
  | @HasTy0.app _ Ψ Φ Γ A B f a h0 h1 =>
    have hsub : SubP S Ψ Φ Γ (app f a) (B.inst a) := fun {Ψ' Φ' Δ σ τ} hσ =>
      by simp only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil]; exact HasTy0.app (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil] using (sub_ty hS h0).2.1 hσ) ((sub_ty hS h1).2.1 hσ)
    ⟨(sub_ty hS h0).1, hsub, fun {Ψ' Φ' Δ σ1 τ1 σ2 τ2} k1 k2 kE =>
      by simp only [inst_subst]; exact EqTm0.app ((sub_ty hS h0).2.2 k1 k2 kE) ((sub_ty hS h1).2.2 k1 k2 kE)⟩
  | @HasTy0.sigma _ Ψ Φ Γ A B l h0 h1 =>
    have hsub : SubP S Ψ Φ Γ (sigma A B) (univ l) := fun {Ψ' Φ' Δ σ τ} hσ =>
      by simp only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil]; exact HasTy0.sigma ((sub_ty hS h0).2.1 hσ) ((sub_ty hS h1).2.1 (hσ.upC hS (sub_ty hS h1).1))
    ⟨(sub_ty hS h0).1, hsub, fun {Ψ' Φ' Δ σ1 τ1 σ2 τ2} k1 k2 kE =>
      by obtain ⟨u1, u2, uE⟩ := TySub.up2 hS k1 k2 kE (sub_ty hS h1).1; exact EqTm0.sigma ((sub_ty hS h0).2.2 k1 k2 kE) ((sub_ty hS h1).2.2 u1 u2 uE)⟩
  | @HasTy0.pair _ Ψ Φ Γ A B a b l h0 h1 h2 =>
    have hsub : SubP S Ψ Φ Γ (pair a b) (sigma A B) := fun {Ψ' Φ' Δ σ τ} hσ =>
      by simp only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil]; exact HasTy0.pair (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil] using (sub_ty hS h0).2.1 hσ) ((sub_ty hS h1).2.1 hσ) (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil] using (sub_ty hS h2).2.1 hσ)
    ⟨(sub_ty hS h0).1, hsub, fun {Ψ' Φ' Δ σ1 τ1 σ2 τ2} k1 k2 kE =>
      by exact EqTm0.pair ((sub_ty hS h0).2.1 k1) ((sub_ty hS h1).2.2 k1 k2 kE) (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil] using (sub_ty hS h2).2.2 k1 k2 kE)⟩
  | @HasTy0.fst _ Ψ Φ Γ A B p h0 =>
    have hsub : SubP S Ψ Φ Γ (fst p) A := fun {Ψ' Φ' Δ σ τ} hσ =>
      by simp only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil]; exact HasTy0.fst (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil] using (sub_ty hS h0).2.1 hσ)
    ⟨(sub_ty hS h0).1, hsub, fun {Ψ' Φ' Δ σ1 τ1 σ2 τ2} k1 k2 kE =>
      EqTm0.fst ((sub_ty hS h0).2.2 k1 k2 kE)⟩
  | @HasTy0.snd _ Ψ Φ Γ A B p h0 =>
    have hsub : SubP S Ψ Φ Γ (snd p) (B.inst (fst p)) := fun {Ψ' Φ' Δ σ τ} hσ =>
      by simp only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil]; exact HasTy0.snd (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil] using (sub_ty hS h0).2.1 hσ)
    ⟨(sub_ty hS h0).1, hsub, fun {Ψ' Φ' Δ σ1 τ1 σ2 τ2} k1 k2 kE =>
      by simp only [inst_subst, Tm.subst]; exact EqTm0.snd ((sub_ty hS h0).2.2 k1 k2 kE)⟩
  | @HasTy0.path _ Ψ Φ Γ A a b l h0 h1 h2 =>
    have hsub : SubP S Ψ Φ Γ (path A a b) (univ l) := fun {Ψ' Φ' Δ σ τ} hσ =>
      by simp only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil]; exact HasTy0.path ((sub_ty hS h0).2.1 (hσ.dup hS)) (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil] using (sub_ty hS h1).2.1 hσ) (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil] using (sub_ty hS h2).2.1 hσ)
    ⟨(sub_ty hS h1).1, hsub, fun {Ψ' Φ' Δ σ1 τ1 σ2 τ2} k1 k2 kE =>
      by simp only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil]; exact EqTm0.path ((sub_ty hS h0).2.2 (k1.dup hS) (k2.dup hS) (kE.dup hS)) (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil] using (sub_ty hS h1).2.2 k1 k2 kE) (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil] using (sub_ty hS h2).2.2 k1 k2 kE)⟩
  | @HasTy0.plam _ Ψ Φ Γ A a b t l h0 h1 h2 h3 =>
    have hsub : SubP S Ψ Φ Γ (plam t) (path A a b) := fun {Ψ' Φ' Δ σ τ} hσ =>
      by simp only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil]; exact HasTy0.plam (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil] using (sub_ty hS h0).2.1 hσ) ((sub_ty hS h1).2.1 (hσ.dup hS)) (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil] using (sub_eq hS h2).2 hσ) (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil] using (sub_eq hS h3).2 hσ)
    ⟨(sub_ty hS h0).1, hsub, fun {Ψ' Φ' Δ σ1 τ1 σ2 τ2} k1 k2 kE =>
      by exact EqTm0.plam ((sub_ty hS h0).2.1 k1) (hsub k1) (HasTy0.conv (hsub k2) (EqTm0.symm ((sub_ty hS h0).2.2 k1 k2 kE))) ((sub_ty hS h1).2.2 (k1.dup hS) (k2.dup hS) (kE.dup hS))⟩
  | @HasTy0.papp _ Ψ Φ Γ A a b p r h0 h1 =>
    have hsub : SubP S Ψ Φ Γ (papp p r) (A.dinst r) := fun {Ψ' Φ' Δ σ τ} hσ =>
      by simp only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil]; exact HasTy0.papp (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil] using (sub_ty hS h0).2.1 hσ) (hσ.sc h1)
    ⟨(sub_ty hS h0).1, hsub, fun {Ψ' Φ' Δ σ1 τ1 σ2 τ2} k1 k2 kE =>
      by simp only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil]; exact EqTm0.papp (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil] using (sub_ty hS h0).2.2 k1 k2 kE) (k1.sc h1) (k2.sc h1) (I_eq_subst_scoped h1 kE.2)⟩
  | @HasTy0.ipi _ Ψ Φ Γ A l h0 h1 =>
    have hsub : SubP S Ψ Φ Γ (ipi A) (univ l) := fun {Ψ' Φ' Δ σ τ} hσ =>
      by simp only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil]; exact HasTy0.ipi hσ.wf ((sub_ty hS h1).2.1 (hσ.dup hS))
    ⟨sub_wf hS h0, hsub, fun {Ψ' Φ' Δ σ1 τ1 σ2 τ2} k1 k2 kE =>
      EqTm0.ipi k1.wf ((sub_ty hS h1).2.2 (k1.dup hS) (k2.dup hS) (kE.dup hS))⟩
  | @HasTy0.ilam _ Ψ Φ Γ A t l h0 h1 =>
    have hsub : SubP S Ψ Φ Γ (plam t) (ipi A) := fun {Ψ' Φ' Δ σ τ} hσ =>
      by simp only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil]; exact HasTy0.ilam (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil] using (sub_ty hS h0).2.1 hσ) ((sub_ty hS h1).2.1 (hσ.dup hS))
    ⟨(sub_ty hS h0).1, hsub, fun {Ψ' Φ' Δ σ1 τ1 σ2 τ2} k1 k2 kE =>
      by exact EqTm0.ilam ((sub_ty hS h0).2.1 k1) ((sub_ty hS h1).2.2 (k1.dup hS) (k2.dup hS) (kE.dup hS))⟩
  | @HasTy0.iapp _ Ψ Φ Γ A p r h0 h1 =>
    have hsub : SubP S Ψ Φ Γ (papp p r) (A.dinst r) := fun {Ψ' Φ' Δ σ τ} hσ =>
      by simp only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil]; exact HasTy0.iapp (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil] using (sub_ty hS h0).2.1 hσ) (hσ.sc h1)
    ⟨(sub_ty hS h0).1, hsub, fun {Ψ' Φ' Δ σ1 τ1 σ2 τ2} k1 k2 kE =>
      by simp only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil]; exact EqTm0.iapp (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil] using (sub_ty hS h0).2.2 k1 k2 kE) (k1.sc h1) (k2.sc h1) (I_eq_subst_scoped h1 kE.2)⟩
  | @HasTy0.split _ Ψ Φ Γ A φ ψ t u l h0 h1 h2 h3 h4 h5 h6 =>
    have hsub : SubP S Ψ Φ Γ (split φ t ψ u) A := fun {Ψ' Φ' Δ σ τ} hσ =>
      by simp only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil]; exact HasTy0.split (hσ.sc h0) (hσ.sc h1) (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil] using (ent_trans hσ.ent (ent_subst h2 _))) ((sub_ty hS h3).2.1 hσ) ((sub_ty hS h4).2.1 (hσ.underCof h0)) ((sub_ty hS h5).2.1 (hσ.underCof h1)) ((sub_eq hS h6).2 ((hσ.underCof h0).underCof h1))
    ⟨(sub_ty hS h3).1, hsub, fun {Ψ' Φ' Δ σ1 τ1 σ2 τ2} k1 k2 kE =>
      by
      have hφ12 := eq_ent (I_eq_subst_scoped h0 kE.2)
      have hψ12 := eq_ent (I_eq_subst_scoped h1 kE.2)
      have hL := hsub k1
      have hR := (HasTy0.conv (hsub k2) (EqTm0.symm ((sub_ty hS h3).2.2 k1 k2 kE)))
      refine EqTm0.local (k1.sc h0) (k1.sc h1) (ent_trans k1.ent (ent_subst h2 _)) hL hR ?_ ?_
      · have hs : (cof Φ' (φ.subst τ1)).Scoped Ψ' := ⟨k1.hscoped, k1.sc h0⟩
        have e1 := EqTm0.splitL (ent_and_right _ _) (HasTy0.restrict hs (ent_and_left _ _) hL)
        have e2 := EqTm0.splitL (ent_trans (ent_and_right _ _) hφ12) (HasTy0.restrict hs (ent_and_left _ _) hR)
        have e3 := (sub_ty hS h4).2.2 (k1.underCof h0) (k2.underCofE (k1.sc h0) hφ12) (kE.underCof k1.hscoped (k1.sc h0))
        exact EqTm0.trans e1 (EqTm0.trans e3 (EqTm0.symm e2))
      · have hs : (cof Φ' (ψ.subst τ1)).Scoped Ψ' := ⟨k1.hscoped, k1.sc h1⟩
        have e1 := EqTm0.splitR (ent_and_right _ _) (HasTy0.restrict hs (ent_and_left _ _) hL)
        have e2 := EqTm0.splitR (ent_trans (ent_and_right _ _) hψ12) (HasTy0.restrict hs (ent_and_left _ _) hR)
        have e3 := (sub_ty hS h5).2.2 (k1.underCof h1) (k2.underCofE (k1.sc h1) hψ12) (kE.underCof k1.hscoped (k1.sc h1))
        exact EqTm0.trans e1 (EqTm0.trans e3 (EqTm0.symm e2))⟩
  | @HasTy0.abort _ Ψ Φ Γ A l h0 h1 =>
    have hsub : SubP S Ψ Φ Γ abort A := fun {Ψ' Φ' Δ σ τ} hσ =>
      HasTy0.abort (ent_trans hσ.ent (ent_subst h0 _)) ((sub_ty hS h1).2.1 hσ)
    ⟨(sub_ty hS h1).1, hsub, fun {Ψ' Φ' Δ σ1 τ1 σ2 τ2} k1 k2 kE =>
      EqTm0.refl (hsub k1)⟩
  | @HasTy0.transp _ Ψ Φ Γ A φ a l h0 h1 h2 h3 =>
    have hsub : SubP S Ψ Φ Γ (transp A φ a) (A.dinst .one) := fun {Ψ' Φ' Δ σ τ} hσ =>
      by simp only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil]; exact HasTy0.transp ((sub_ty hS h0).2.1 (hσ.dup hS)) (hσ.sc h1) (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil] using (sub_eq hS h2).2 ((hσ.underCof h1).dup hS)) (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil] using (sub_ty hS h3).2.1 hσ)
    ⟨(sub_ty hS h3).1, hsub, fun {Ψ' Φ' Δ σ1 τ1 σ2 τ2} k1 k2 kE =>
      by
      have hφ12 := eq_ent (I_eq_subst_scoped h1 kE.2)
      have hφ21 := eq_ent (I_eq_subst_scoped h1 (fun i hi => I_eq_symm (kE.2 i hi)))
      have hA1 := (sub_ty hS h0).2.2 (k1.inst (r := .one) trivial) (k2.inst (r := .one) trivial) (kE.inst (I_eq_refl _))
      rw [← dinst_one_consI, ← dinst_one_consI] at hA1
      have hT1 := hsub k1
      have hT2 := hsub k2
      simp only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil] at hA1 hT1 hT2 ⊢
      exact EqTm0.transp hT1 (HasTy0.conv hT2 (EqTm0.symm hA1))
        ((sub_ty hS h0).2.2 (k1.dup hS) (k2.dup hS) (kE.dup hS)) hφ12 hφ21 (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil] using (sub_ty hS h3).2.2 k1 k2 kE)⟩
  | @HasTy0.hcomp _ Ψ Φ Γ A φ u a l h0 h1 h2 h3 h4 =>
    have hsub : SubP S Ψ Φ Γ (hcomp A φ u a) A := fun {Ψ' Φ' Δ σ τ} hσ =>
      by simp only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil]; exact HasTy0.hcomp ((sub_ty hS h0).2.1 hσ) (hσ.sc h1) (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil] using (sub_ty hS h2).2.1 ((hσ.underCof h1).dup hS)) ((sub_ty hS h3).2.1 hσ) (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil] using (sub_eq hS h4).2 (hσ.underCof h1))
    ⟨(sub_ty hS h0).1, hsub, fun {Ψ' Φ' Δ σ1 τ1 σ2 τ2} k1 k2 kE =>
      by
      have hφ12 := eq_ent (I_eq_subst_scoped h1 kE.2)
      have hφ21 := eq_ent (I_eq_subst_scoped h1 (fun i hi => I_eq_symm (kE.2 i hi)))
      have hu := (sub_ty hS h2).2.2 ((k1.underCof h1).dup hS) ((k2.underCofE (k1.sc h1) hφ12).dup hS)
        ((kE.underCof k1.hscoped (k1.sc h1)).dup hS)
      simp only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil] at hu ⊢
      exact EqTm0.hcomp (hsub k1) (HasTy0.conv (hsub k2) (EqTm0.symm ((sub_ty hS h0).2.2 k1 k2 kE))) ((sub_ty hS h0).2.2 k1 k2 kE) hφ12 hφ21 hu ((sub_ty hS h3).2.2 k1 k2 kE)⟩
  | @HasTy0.glue _ Ψ Φ Γ A φ T e l h0 h1 h2 h3 =>
    have hsub : SubP S Ψ Φ Γ (glue A φ T e) (univ l) := fun {Ψ' Φ' Δ σ τ} hσ =>
      by simp only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil]; exact HasTy0.glue ((sub_ty hS h0).2.1 hσ) (hσ.sc h1) ((sub_ty hS h2).2.1 (hσ.underCof h1)) (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil] using (sub_ty hS h3).2.1 (hσ.underCof h1))
    ⟨(sub_ty hS h0).1, hsub, fun {Ψ' Φ' Δ σ1 τ1 σ2 τ2} k1 k2 kE =>
      by
      have hφ12 := eq_ent (I_eq_subst_scoped h1 kE.2)
      have hφ21 := eq_ent (I_eq_subst_scoped h1 (fun i hi => I_eq_symm (kE.2 i hi)))
      have he := (sub_ty hS h3).2.2 (k1.underCof h1) (k2.underCofE (k1.sc h1) hφ12) (kE.underCof k1.hscoped (k1.sc h1))
      simp only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil] at he ⊢
      exact EqTm0.glue (hsub k1) (hsub k2) ((sub_ty hS h0).2.2 k1 k2 kE) hφ12 hφ21 ((sub_ty hS h2).2.2 (k1.underCof h1) (k2.underCofE (k1.sc h1) hφ12) (kE.underCof k1.hscoped (k1.sc h1))) he⟩
  | @HasTy0.glueEl _ Ψ Φ Γ A φ T e t a l h0 h1 h2 h3 h4 =>
    have hsub : SubP S Ψ Φ Γ (glueEl φ e t a) (glue A φ T e) := fun {Ψ' Φ' Δ σ τ} hσ =>
      by have hφ := scoped_cof_right (scoped_of_ty h1); simp only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil]; exact HasTy0.glueEl (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil] using (sub_ty hS h0).2.1 hσ) (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil] using (sub_ty hS h1).2.1 (hσ.underCof hφ)) ((sub_ty hS h2).2.1 (hσ.underCof hφ)) ((sub_ty hS h3).2.1 hσ) (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil] using (sub_eq hS h4).2 (hσ.underCof hφ))
    ⟨(sub_ty hS h0).1, hsub, fun {Ψ' Φ' Δ σ1 τ1 σ2 τ2} k1 k2 kE =>
      by
      have hφ := scoped_cof_right (scoped_of_ty h1)
      have hφ12 := eq_ent (I_eq_subst_scoped hφ kE.2)
      have hφ21 := eq_ent (I_eq_subst_scoped hφ (fun i hi => I_eq_symm (kE.2 i hi)))
      have he := (sub_ty hS h1).2.2 (k1.underCof hφ) (k2.underCofE (k1.sc hφ) hφ12) (kE.underCof k1.hscoped (k1.sc hφ))
      simp only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil] at he ⊢
      exact EqTm0.glueEl (hsub k1) (HasTy0.conv (hsub k2) (EqTm0.symm ((sub_ty hS h0).2.2 k1 k2 kE))) hφ12 hφ21 he ((sub_ty hS h2).2.2 (k1.underCof hφ) (k2.underCofE (k1.sc hφ) hφ12) (kE.underCof k1.hscoped (k1.sc hφ))) ((sub_ty hS h3).2.2 k1 k2 kE)⟩
  | @HasTy0.unglue _ Ψ Φ Γ A φ T e g l h0 h1 h2 h3 =>
    have hsub : SubP S Ψ Φ Γ (unglue φ e g) A := fun {Ψ' Φ' Δ σ τ} hσ =>
      by have hφ := scoped_cof_right (scoped_of_ty h2); simp only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil]; exact HasTy0.unglue (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil] using (sub_ty hS h0).2.1 hσ) ((sub_ty hS h1).2.1 hσ) (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil] using (sub_ty hS h2).2.1 (hσ.underCof hφ)) (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil] using (sub_ty hS h3).2.1 hσ)
    ⟨(sub_ty hS h0).1, hsub, fun {Ψ' Φ' Δ σ1 τ1 σ2 τ2} k1 k2 kE =>
      by
      have hφ := scoped_cof_right (scoped_of_ty h2)
      have hφ12 := eq_ent (I_eq_subst_scoped hφ kE.2)
      have hφ21 := eq_ent (I_eq_subst_scoped hφ (fun i hi => I_eq_symm (kE.2 i hi)))
      have he := (sub_ty hS h2).2.2 (k1.underCof hφ) (k2.underCofE (k1.sc hφ) hφ12) (kE.underCof k1.hscoped (k1.sc hφ))
      simp only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil] at he ⊢
      exact EqTm0.unglue (hsub k1) (HasTy0.conv (hsub k2) (EqTm0.symm ((sub_ty hS h1).2.2 k1 k2 kE))) hφ12 hφ21 he (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil] using (sub_ty hS h3).2.2 k1 k2 kE)⟩
  | @HasTy0.data _ Ψ Φ Γ d D ps h0 h1 h2 =>
    have hsub : SubP S Ψ Φ Γ (data d ps) (univ D.level) := fun {Ψ' Φ' Δ σ τ} hσ =>
      by simp only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil]; exact HasTy0.data h0 h1 (((sub_tele hS h2).2 (fun k A hk => by simpa using hS.params _ _ _ _ h0 hk)).1 hσ)
    ⟨(sub_tele hS h2).1, hsub, fun {Ψ' Φ' Δ σ1 τ1 σ2 τ2} k1 k2 kE =>
      EqTm0.data h0 (hsub k1) (hsub k2) (((sub_tele hS h2).2 (fun k A hk => by simpa using hS.params _ _ _ _ h0 hk)).2 k1 k2 kE)⟩
  | @HasTy0.con _ Ψ Φ Γ d D c C ps args rs h0 h1 h2 h3 h4 h5 h6 h7 =>
    have hsub : SubP S Ψ Φ Γ (con d c ps args rs) (data d ps) := fun {Ψ' Φ' Δ σ τ} hσ =>
      by
      have hlen := tele_length h4
      have ht := ((sub_tele hS h5).2 (fun k A hk => by
        rw [List.length_reverse, hlen]; exact argTys_closed hS h0 h1 k A hk)).1 hσ
      simp only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil]
      refine HasTy0.con h0 h1 (isList_subst h2 _ _) ((sub_ty hS h3).2.1 hσ) (((sub_tele hS h4).2 (fun k A hk => by simpa using hS.params _ _ _ _ h0 hk)).1 hσ) ?_
        (by simpa using h6) (fun r hr => ?_)
      · rw [toList_subst h2, ← List.map_reverse]; exact ht
      · obtain ⟨r0, hr0, rfl⟩ := List.mem_map.1 hr; exact hσ.sc (h7 r0 hr0)
    ⟨(sub_ty hS h3).1, hsub, fun {Ψ' Φ' Δ σ1 τ1 σ2 τ2} k1 k2 kE =>
      by
      have hlen := tele_length h4
      have ht := ((sub_tele hS h5).2 (fun k A hk => by
        rw [List.length_reverse, hlen]; exact argTys_closed hS h0 h1 k A hk)).2 k1 k2 kE
      refine EqTm0.con h0 h1 (hsub k1) (HasTy0.conv (hsub k2) (EqTm0.symm ((sub_ty hS h3).2.2 k1 k2 kE))) (((sub_tele hS h4).2 (fun k A hk => by simpa using hS.params _ _ _ _ h0 hk)).2 k1 k2 kE) ?_
        (by simp) ?_
      · rw [toList_subst h2, ← List.map_reverse]; exact ht
      · intro k r r' hr hr'
        rw [List.getElem?_map] at hr hr'
        obtain ⟨r0, hr0, rfl⟩ := Option.map_eq_some_iff.1 hr
        obtain ⟨r0', hr0', rfl⟩ := Option.map_eq_some_iff.1 hr'
        rw [hr0] at hr0'; cases hr0'
        exact I_eq_subst_scoped (h7 r0 (List.mem_of_getElem? hr0)) kE.2⟩
  | @HasTy0.elim _ Ψ Φ Γ d D ps P bs t m h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 =>
    have hsub : SubP S Ψ Φ Γ (elim d ps P bs t) (P.inst t) := fun {Ψ' Φ' Δ σ τ} hσ =>
      by
      have hlen := tele_length h3
      simp only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil]
      refine HasTy0.elim h0 (isList_subst h1 _ _) ((sub_ty hS h2).2.1 hσ) (((sub_tele hS h3).2 (fun k A hk => by simpa using hS.params _ _ _ _ h0 hk)).1 hσ)
        ((sub_ty hS h4).2.1 (hσ.upC hS (sub_ty hS h4).1)) (isList_subst h5 _ _)
        (by rw [toList_subst h5, List.length_map, h6]) ?_ ?_ ((sub_ty hS h9).2.1 hσ)
      · intro c C b hc hb
        rw [toList_subst h5, List.getElem?_map] at hb
        obtain ⟨b0, hb0, rfl⟩ := Option.map_eq_some_iff.1 hb
        have := (sub_ty hS (h7 c C b0 hc hb0)).2.1 hσ
        rwa [branchTy_subst _ _ hS h0 hc h1 hlen] at this
      · intro c C b k ψ e hc hb hk
        rw [toList_subst h5, List.getElem?_map] at hb
        obtain ⟨b0, hb0, rfl⟩ := Option.map_eq_some_iff.1 hb
        have hψ := hS.bnd _ _ _ _ _ _ _ h0 hc hk
        have := (sub_eq hS (h8 c C b0 k ψ e hc hb0 hk)).2
          (hσ.branch hS h0 hc h1 hlen hψ.1 (sub_eq hS (h8 c C b0 k ψ e hc hb0 hk)).1)
        rw [branchApp_subst, bndElim_subst _ _ h1 hlen h5 e hψ.2, branchBody_subst] at this
        exact this
    ⟨(sub_ty hS h2).1, hsub, fun {Ψ' Φ' Δ σ1 τ1 σ2 τ2} k1 k2 kE =>
      by
      have hlen := tele_length h3
      obtain ⟨_, _, hdata, _, _⟩ := (sub_ty hS h4).1
      obtain ⟨u1, u2, uE⟩ := TySub.up2 hS k1 k2 kE (sub_ty hS h4).1
      have hP := (sub_ty hS h4).2.2 (k1.cons ((sub_ty hS h9).2.1 k1)) (k2.cons ((sub_ty hS h9).2.1 k2)) (kE.cons ((sub_ty hS h9).2.2 k1 k2 kE))
      rw [← inst_consT, ← inst_consT] at hP
      have hel1 := hsub k1
      have hel2 := HasTy0.conv (hsub k2) (EqTm0.symm hP)
      simp only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil] at hel1 hel2 ⊢
      refine EqTm0.elim h0 hel1 hel2
        (((sub_tele hS h3).2 (fun k A hk => by simpa using hS.params _ _ _ _ h0 hk)).2 k1 k2 kE) ((sub_ty hS h4).2.2 u1 u2 uE) (isList_subst h5 _ _) (isList_subst h5 _ _)
        (by rw [toList_subst h5, toList_subst h5, List.length_map, List.length_map]) ?_ (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil] using (sub_ty hS h9).2.2 k1 k2 kE)
      intro c C b b' hc hb hb'
      rw [toList_subst h5, List.getElem?_map] at hb hb'
      obtain ⟨b0, hb0, rfl⟩ := Option.map_eq_some_iff.1 hb
      obtain ⟨b0', hb0', rfl⟩ := Option.map_eq_some_iff.1 hb'
      rw [hb0] at hb0'; cases hb0'
      have := (sub_ty hS (h7 c C b0 hc hb0)).2.2 k1 k2 kE
      rwa [branchTy_subst _ _ hS h0 hc h1 hlen] at this⟩

theorem sub_tele (hS : SigClosed S) {Ψ Φ Γ ts Δt prev} : HasTele0 S Ψ Φ Γ ts Δt prev →
    CtxSub S Ψ Φ Γ ∧ ((∀ (k : Nat) (A : Tm), Δt[k]? = some A → A.closedB (prev.length + k) 0 = true) →
      (∀ {Ψ' Φ' Δ σ τ}, TySub S Ψ Φ Γ Ψ' Φ' Δ σ τ →
        HasTele0 S Ψ' Φ' Δ (ts.subst σ τ) Δt (prev.map (·.subst σ τ))) ∧
      (∀ {Ψ' Φ' Δ σ1 τ1 σ2 τ2}, TySub S Ψ Φ Γ Ψ' Φ' Δ σ1 τ1 → TySub S Ψ Φ Γ Ψ' Φ' Δ σ2 τ2 →
        EqSub S Ψ Γ Ψ' Φ' Δ σ1 τ1 σ2 τ2 →
        EqTele0 S Ψ' Φ' Δ (ts.subst σ1 τ1) (ts.subst σ2 τ2) Δt (prev.map (·.subst σ1 τ1))))
  | .nil h0 => ⟨sub_wf hS h0, fun hcl =>
      ⟨fun hσ => HasTele0.nil hσ.wf, fun k1 k2 kE => EqTele0.nil k1.wf⟩⟩
  | .cons h0 h1 => ⟨(sub_ty hS h0).1, fun hcl =>
      ⟨fun hσ => by
        have hA := tele_closed_head hcl
        have := (sub_ty hS h0).2.1 hσ
        rw [substList_subst hA] at this
        exact HasTele0.cons this (((sub_tele hS h1).2 (tele_closed_tail hcl)).1 hσ),
      fun k1 k2 kE => by
        have hA := tele_closed_head hcl
        have := (sub_ty hS h0).2.2 k1 k2 kE
        rw [substList_subst hA] at this
        exact EqTele0.cons this (((sub_tele hS h1).2 (tele_closed_tail hcl)).2 k1 k2 kE)⟩⟩

theorem sub_eqtele (hS : SigClosed S) {Ψ Φ Γ ts ts' Δt prev} : EqTele0 S Ψ Φ Γ ts ts' Δt prev →
    CtxSub S Ψ Φ Γ ∧ ((∀ (k : Nat) (A : Tm), Δt[k]? = some A → A.closedB (prev.length + k) 0 = true) →
      ∀ {Ψ' Φ' Δ σ τ}, TySub S Ψ Φ Γ Ψ' Φ' Δ σ τ →
        EqTele0 S Ψ' Φ' Δ (ts.subst σ τ) (ts'.subst σ τ) Δt (prev.map (·.subst σ τ)))
  | .nil h0 => ⟨sub_wf hS h0, fun hcl =>
      fun hσ => EqTele0.nil hσ.wf⟩
  | .cons h0 h1 => ⟨(sub_eq hS h0).1, fun hcl =>
      fun hσ => by
        have hA := tele_closed_head hcl
        have := (sub_eq hS h0).2 hσ
        rw [substList_subst hA] at this
        exact EqTele0.cons this ((sub_eqtele hS h1).2 (tele_closed_tail hcl) hσ)⟩
  | .dataInj h0 h1 h2 h3 => ⟨(sub_tele hS h1).1, fun hcl =>
      fun hσ => by simp only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil]; exact EqTele0.dataInj h0 (((sub_tele hS h1).2 (fun k A hk => by simpa using hS.params _ _ _ _ h0 hk)).1 hσ) (((sub_tele hS h2).2 (fun k A hk => by simpa using hS.params _ _ _ _ h0 hk)).1 hσ) (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil] using (sub_eq hS h3).2 hσ)⟩

theorem sub_eq (hS : SigClosed S) {Ψ Φ Γ t u A} : EqTm0 S Ψ Φ Γ t u A → CtxSub S Ψ Φ Γ ∧
    ∀ {Ψ' Φ' Δ σ τ}, TySub S Ψ Φ Γ Ψ' Φ' Δ σ τ →
      EqTm0 S Ψ' Φ' Δ (t.subst σ τ) (u.subst σ τ) (A.subst σ τ)
  | @EqTm0.refl _ Ψ Φ Γ t A h0 => ⟨(sub_ty hS h0).1, fun {Ψ' Φ' Δ σ τ} hσ =>
    EqTm0.refl ((sub_ty hS h0).2.1 hσ)⟩
  | @EqTm0.symm _ Ψ Φ Γ t u A h0 => ⟨(sub_eq hS h0).1, fun {Ψ' Φ' Δ σ τ} hσ =>
    EqTm0.symm ((sub_eq hS h0).2 hσ)⟩
  | @EqTm0.trans _ Ψ Φ Γ t u v A h0 h1 => ⟨(sub_eq hS h0).1, fun {Ψ' Φ' Δ σ τ} hσ =>
    EqTm0.trans ((sub_eq hS h0).2 hσ) ((sub_eq hS h1).2 hσ)⟩
  | @EqTm0.conv _ Ψ Φ Γ t u A B l h0 h1 => ⟨(sub_eq hS h0).1, fun {Ψ' Φ' Δ σ τ} hσ =>
    EqTm0.conv ((sub_eq hS h0).2 hσ) ((sub_eq hS h1).2 hσ)⟩
  | @EqTm0.restrict _ Ψ Φ Φ' Γ t u A h0 h1 h2 => ⟨CtxSub.restrictSrc h1 (sub_eq hS h2).1, fun {Ψ' Φ' Δ σ τ} hσ =>
    (sub_eq hS h2).2 (hσ.restrictSrc h1)⟩
  | @EqTm0.cumul _ Ψ Φ Γ A B l h0 h1 => ⟨(sub_eq hS h1).1, fun {Ψ' Φ' Δ σ τ} hσ =>
    EqTm0.cumul h0 ((sub_eq hS h1).2 hσ)⟩
  | @EqTm0.delta _ Ψ Φ Γ k t A h0 h1 => ⟨(sub_ty hS h0).1, fun {Ψ' Φ' Δ σ τ} hσ =>
    by
      obtain ⟨ht, hA⟩ := hS.defn _ _ _ h1
      rw [closed_subst_id hA (fun _ h => absurd h (Nat.not_lt_zero _)) (fun _ h => absurd h (Nat.not_lt_zero _)), closed_subst_id ht (fun _ h => absurd h (Nat.not_lt_zero _)) (fun _ h => absurd h (Nat.not_lt_zero _))]
      have := ((sub_ty hS h0).2.1 hσ)
      rw [closed_subst_id hA (fun _ h => absurd h (Nat.not_lt_zero _)) (fun _ h => absurd h (Nat.not_lt_zero _))] at this
      exact EqTm0.delta this h1⟩
  | @EqTm0.absurd _ Ψ Φ Γ t u A h0 h1 h2 => ⟨(sub_ty hS h1).1, fun {Ψ' Φ' Δ σ τ} hσ =>
    EqTm0.absurd (ent_trans hσ.ent (ent_subst h0 _)) ((sub_ty hS h1).2.1 hσ) ((sub_ty hS h2).2.1 hσ)⟩
  | @EqTm0.local _ Ψ Φ Γ φ ψ t u A h0 h1 h2 h3 h4 h5 h6 => ⟨(sub_ty hS h3).1, fun {Ψ' Φ' Δ σ τ} hσ =>
    by exact EqTm0.local (hσ.sc h0) (hσ.sc h1) (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil] using (ent_trans hσ.ent (ent_subst h2 _))) ((sub_ty hS h3).2.1 hσ) ((sub_ty hS h4).2.1 hσ) ((sub_eq hS h5).2 (hσ.underCof h0)) ((sub_eq hS h6).2 (hσ.underCof h1))⟩
  | @EqTm0.face _ Ψ Φ Γ t A i d l h0 h1 h2 h3 => ⟨(sub_ty hS h2).1, fun {Ψ' Φ' Δ σ τ} hσ =>
    by
      have hΦ := scoped_of_ty h3
      rw [face_dset_subst]
      have hT : TyFace S _ _ _ _ := Or.inr ⟨_, (sub_ty hS h2).2.1,
        face_lemma hΦ (sub_ty hS h2).1 (sub_ty hS h2).2.1 (sub_ty hS h2).2.2 (Or.inl ⟨_, rfl⟩)⟩
      have hf := faceEq_lit (Ψ := Ψ) (ent_trans hσ.ent (ent_subst h1 τ))
      refine face_lemma hΦ (sub_ty hS h3).1 (sub_ty hS h3).2.1 (sub_ty hS h3).2.2 hT hσ
        (hσ.transfer hΦ (sub_ty hS h3).1 (fun j hj => ?_) hf) hf
      by_cases hji : j = i
      · simp only [hji, if_true]; cases d <;> trivial
      · simp only [hji, if_false]; exact hσ.bound j hj⟩
  | @EqTm0.faceU _ Ψ Φ Γ t i d l h0 h1 h2 => ⟨(sub_ty hS h2).1, fun {Ψ' Φ' Δ σ τ} hσ =>
    by
      have hΦ := scoped_of_ty h2
      rw [face_dset_subst]
      have hf := faceEq_lit (Ψ := Ψ) (ent_trans hσ.ent (ent_subst h1 τ))
      refine face_lemma hΦ (sub_ty hS h2).1 (sub_ty hS h2).2.1 (sub_ty hS h2).2.2 (Or.inl ⟨_, rfl⟩) hσ
        (hσ.transfer hΦ (sub_ty hS h2).1 (fun j hj => ?_) hf) hf
      by_cases hji : j = i
      · simp only [hji, if_true]; cases d <;> trivial
      · simp only [hji, if_false]; exact hσ.bound j hj⟩
  | @EqTm0.pi _ Ψ Φ Γ A A' B B' l h0 h1 => ⟨(sub_eq hS h0).1, fun {Ψ' Φ' Δ σ τ} hσ =>
    by simp only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil]; exact EqTm0.pi ((sub_eq hS h0).2 hσ) ((sub_eq hS h1).2 (hσ.upC hS (sub_eq hS h1).1))⟩
  | @EqTm0.lam _ Ψ Φ Γ A B t t' l h0 h1 => ⟨(sub_ty hS h0).1, fun {Ψ' Φ' Δ σ τ} hσ =>
    by simp only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil]; exact EqTm0.lam (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil] using (sub_ty hS h0).2.1 hσ) ((sub_eq hS h1).2 (hσ.upC hS (sub_eq hS h1).1))⟩
  | @EqTm0.app _ Ψ Φ Γ A B f f' a a' h0 h1 => ⟨(sub_eq hS h0).1, fun {Ψ' Φ' Δ σ τ} hσ =>
    by simp only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil]; exact EqTm0.app (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil] using (sub_eq hS h0).2 hσ) ((sub_eq hS h1).2 hσ)⟩
  | @EqTm0.sigma _ Ψ Φ Γ A A' B B' l h0 h1 => ⟨(sub_eq hS h0).1, fun {Ψ' Φ' Δ σ τ} hσ =>
    by simp only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil]; exact EqTm0.sigma ((sub_eq hS h0).2 hσ) ((sub_eq hS h1).2 (hσ.upC hS (sub_eq hS h1).1))⟩
  | @EqTm0.pair _ Ψ Φ Γ A B a a' b b' l h0 h1 h2 => ⟨(sub_ty hS h0).1, fun {Ψ' Φ' Δ σ τ} hσ =>
    by simp only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil]; exact EqTm0.pair (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil] using (sub_ty hS h0).2.1 hσ) ((sub_eq hS h1).2 hσ) (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil] using (sub_eq hS h2).2 hσ)⟩
  | @EqTm0.fst _ Ψ Φ Γ A B p p' h0 => ⟨(sub_eq hS h0).1, fun {Ψ' Φ' Δ σ τ} hσ =>
    by simp only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil]; exact EqTm0.fst (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil] using (sub_eq hS h0).2 hσ)⟩
  | @EqTm0.snd _ Ψ Φ Γ A B p p' h0 => ⟨(sub_eq hS h0).1, fun {Ψ' Φ' Δ σ τ} hσ =>
    by simp only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil]; exact EqTm0.snd (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil] using (sub_eq hS h0).2 hσ)⟩
  | @EqTm0.path _ Ψ Φ Γ A A' a a' b b' l h0 h1 h2 => ⟨(sub_eq hS h1).1, fun {Ψ' Φ' Δ σ τ} hσ =>
    by simp only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil]; exact EqTm0.path ((sub_eq hS h0).2 (hσ.dup hS)) (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil] using (sub_eq hS h1).2 hσ) (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil] using (sub_eq hS h2).2 hσ)⟩
  | @EqTm0.plam _ Ψ Φ Γ A a b t t' l h0 h1 h2 h3 => ⟨(sub_ty hS h0).1, fun {Ψ' Φ' Δ σ τ} hσ =>
    by simp only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil]; exact EqTm0.plam (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil] using (sub_ty hS h0).2.1 hσ) (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil] using (sub_ty hS h1).2.1 hσ) (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil] using (sub_ty hS h2).2.1 hσ) ((sub_eq hS h3).2 (hσ.dup hS))⟩
  | @EqTm0.papp _ Ψ Φ Γ A a b p p' r r' h0 h1 h2 h3 => ⟨(sub_eq hS h0).1, fun {Ψ' Φ' Δ σ τ} hσ =>
    by simp only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil]; exact EqTm0.papp (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil] using (sub_eq hS h0).2 hσ) (hσ.sc h1) (hσ.sc h2) (I_eq_subst h3 _)⟩
  | @EqTm0.split _ Ψ Φ Γ A φ ψ t t' u u' h0 h1 h2 h3 => ⟨(sub_ty hS h0).1, fun {Ψ' Φ' Δ σ τ} hσ =>
    by have hφ := scoped_cof_right (scoped_of_eq h2); have hψ := scoped_cof_right (scoped_of_eq h3); simp only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil]; exact EqTm0.split (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil] using (sub_ty hS h0).2.1 hσ) (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil] using (sub_ty hS h1).2.1 hσ) ((sub_eq hS h2).2 (hσ.underCof hφ)) ((sub_eq hS h3).2 (hσ.underCof hψ))⟩
  | @EqTm0.transp _ Ψ Φ Γ A A' φ φ' a a' l h0 h1 h2 h3 h4 h5 => ⟨(sub_ty hS h0).1, fun {Ψ' Φ' Δ σ τ} hσ =>
    by simp only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil]; exact EqTm0.transp (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil] using (sub_ty hS h0).2.1 hσ) (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil] using (sub_ty hS h1).2.1 hσ) ((sub_eq hS h2).2 (hσ.dup hS)) (ent_subst h3 _) (ent_subst h4 _) (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil] using (sub_eq hS h5).2 hσ)⟩
  | @EqTm0.hcomp _ Ψ Φ Γ A A' φ φ' u u' a a' l h0 h1 h2 h3 h4 h5 h6 => ⟨(sub_ty hS h0).1, fun {Ψ' Φ' Δ σ τ} hσ =>
    by have hφ := scoped_cof_shift_right (scoped_of_eq h5); simp only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil]; exact EqTm0.hcomp (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil] using (sub_ty hS h0).2.1 hσ) (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil] using (sub_ty hS h1).2.1 hσ) ((sub_eq hS h2).2 hσ) (ent_subst h3 _) (ent_subst h4 _) (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil] using (sub_eq hS h5).2 ((hσ.underCof hφ).dup hS)) ((sub_eq hS h6).2 hσ)⟩
  | @EqTm0.glue _ Ψ Φ Γ A A' φ φ' T T' e e' l h0 h1 h2 h3 h4 h5 h6 => ⟨(sub_ty hS h0).1, fun {Ψ' Φ' Δ σ τ} hσ =>
    by have hφ := scoped_cof_right (scoped_of_eq h5); simp only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil]; exact EqTm0.glue (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil] using (sub_ty hS h0).2.1 hσ) (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil] using (sub_ty hS h1).2.1 hσ) ((sub_eq hS h2).2 hσ) (ent_subst h3 _) (ent_subst h4 _) ((sub_eq hS h5).2 (hσ.underCof hφ)) (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil] using (sub_eq hS h6).2 (hσ.underCof hφ))⟩
  | @EqTm0.glueEl _ Ψ Φ Γ φ φ' t t' a a' A T e e' h0 h1 h2 h3 h4 h5 h6 => ⟨(sub_ty hS h0).1, fun {Ψ' Φ' Δ σ τ} hσ =>
    by have hφ := scoped_cof_right (scoped_of_eq h4); simp only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil]; exact EqTm0.glueEl (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil] using (sub_ty hS h0).2.1 hσ) (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil] using (sub_ty hS h1).2.1 hσ) (ent_subst h2 _) (ent_subst h3 _) (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil] using (sub_eq hS h4).2 (hσ.underCof hφ)) ((sub_eq hS h5).2 (hσ.underCof hφ)) ((sub_eq hS h6).2 hσ)⟩
  | @EqTm0.unglue _ Ψ Φ Γ A φ φ' T e e' g g' h0 h1 h2 h3 h4 h5 => ⟨(sub_ty hS h0).1, fun {Ψ' Φ' Δ σ τ} hσ =>
    by have hφ := scoped_cof_right (scoped_of_eq h4); simp only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil]; exact EqTm0.unglue (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil] using (sub_ty hS h0).2.1 hσ) (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil] using (sub_ty hS h1).2.1 hσ) (ent_subst h2 _) (ent_subst h3 _) (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil] using (sub_eq hS h4).2 (hσ.underCof hφ)) (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil] using (sub_eq hS h5).2 hσ)⟩
  | @EqTm0.ipi _ Ψ Φ Γ A A' l h0 h1 => ⟨sub_wf hS h0, fun {Ψ' Φ' Δ σ τ} hσ =>
    by simp only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil]; exact EqTm0.ipi hσ.wf ((sub_eq hS h1).2 (hσ.dup hS))⟩
  | @EqTm0.ilam _ Ψ Φ Γ A t t' l h0 h1 => ⟨(sub_ty hS h0).1, fun {Ψ' Φ' Δ σ τ} hσ =>
    by simp only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil]; exact EqTm0.ilam (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil] using (sub_ty hS h0).2.1 hσ) ((sub_eq hS h1).2 (hσ.dup hS))⟩
  | @EqTm0.iapp _ Ψ Φ Γ A p p' r r' h0 h1 h2 h3 => ⟨(sub_eq hS h0).1, fun {Ψ' Φ' Δ σ τ} hσ =>
    by simp only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil]; exact EqTm0.iapp (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil] using (sub_eq hS h0).2 hσ) (hσ.sc h1) (hσ.sc h2) (I_eq_subst h3 _)⟩
  | @EqTm0.piInjDom _ Ψ Φ Γ A A' B B' l h0 => ⟨(sub_eq hS h0).1, fun {Ψ' Φ' Δ σ τ} hσ =>
    by simp only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil]; exact EqTm0.piInjDom (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil] using (sub_eq hS h0).2 hσ)⟩
  | @EqTm0.piInjCod _ Ψ Φ Γ A A' B B' a l h0 h1 => ⟨(sub_eq hS h0).1, fun {Ψ' Φ' Δ σ τ} hσ =>
    by simp only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil]; exact EqTm0.piInjCod (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil] using (sub_eq hS h0).2 hσ) ((sub_ty hS h1).2.1 hσ)⟩
  | @EqTm0.sigmaInjDom _ Ψ Φ Γ A A' B B' l h0 => ⟨(sub_eq hS h0).1, fun {Ψ' Φ' Δ σ τ} hσ =>
    by simp only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil]; exact EqTm0.sigmaInjDom (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil] using (sub_eq hS h0).2 hσ)⟩
  | @EqTm0.sigmaInjCod _ Ψ Φ Γ A A' B B' a l h0 h1 => ⟨(sub_eq hS h0).1, fun {Ψ' Φ' Δ σ τ} hσ =>
    by simp only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil]; exact EqTm0.sigmaInjCod (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil] using (sub_eq hS h0).2 hσ) ((sub_ty hS h1).2.1 hσ)⟩
  | @EqTm0.pathInjLine _ Ψ Φ Γ A A' a a' b b' r l h0 h1 => ⟨(sub_eq hS h0).1, fun {Ψ' Φ' Δ σ τ} hσ =>
    by simp only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil]; exact EqTm0.pathInjLine (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil] using (sub_eq hS h0).2 hσ) (hσ.sc h1)⟩
  | @EqTm0.pathInjLeft _ Ψ Φ Γ A A' a a' b b' l h0 => ⟨(sub_eq hS h0).1, fun {Ψ' Φ' Δ σ τ} hσ =>
    by simp only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil]; exact EqTm0.pathInjLeft (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil] using (sub_eq hS h0).2 hσ)⟩
  | @EqTm0.pathInjRight _ Ψ Φ Γ A A' a a' b b' l h0 => ⟨(sub_eq hS h0).1, fun {Ψ' Φ' Δ σ τ} hσ =>
    by simp only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil]; exact EqTm0.pathInjRight (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil] using (sub_eq hS h0).2 hσ)⟩
  | @EqTm0.ipiInj _ Ψ Φ Γ A A' r l h0 h1 => ⟨(sub_eq hS h0).1, fun {Ψ' Φ' Δ σ τ} hσ =>
    by simp only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil]; exact EqTm0.ipiInj (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil] using (sub_eq hS h0).2 hσ) (hσ.sc h1)⟩
  | @EqTm0.noConf _ Ψ Φ Γ X Y l t u T h0 h1 h2 h3 => ⟨(sub_eq hS h1).1, fun {Ψ' Φ' Δ σ τ} hσ =>
    EqTm0.noConf (headClash_subst _ _ h0) ((sub_eq hS h1).2 hσ) ((sub_ty hS h2).2.1 hσ) ((sub_ty hS h3).2.1 hσ)⟩
  | @EqTm0.piBeta _ Ψ Φ Γ A t a T h0 => ⟨(sub_ty hS h0).1, fun {Ψ' Φ' Δ σ τ} hσ =>
    by simp only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil]; exact EqTm0.piBeta (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil] using (sub_ty hS h0).2.1 hσ)⟩
  | @EqTm0.piEta _ Ψ Φ Γ A B f h0 => ⟨(sub_ty hS h0).1, fun {Ψ' Φ' Δ σ τ} hσ =>
    by simp only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil]; exact EqTm0.piEta (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil] using (sub_ty hS h0).2.1 hσ)⟩
  | @EqTm0.fstBeta _ Ψ Φ Γ a b T h0 => ⟨(sub_ty hS h0).1, fun {Ψ' Φ' Δ σ τ} hσ =>
    by simp only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil]; exact EqTm0.fstBeta (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil] using (sub_ty hS h0).2.1 hσ)⟩
  | @EqTm0.sndBeta _ Ψ Φ Γ a b T h0 => ⟨(sub_ty hS h0).1, fun {Ψ' Φ' Δ σ τ} hσ =>
    by simp only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil]; exact EqTm0.sndBeta (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil] using (sub_ty hS h0).2.1 hσ)⟩
  | @EqTm0.sigmaEta _ Ψ Φ Γ A B p h0 => ⟨(sub_ty hS h0).1, fun {Ψ' Φ' Δ σ τ} hσ =>
    by simp only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil]; exact EqTm0.sigmaEta (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil] using (sub_ty hS h0).2.1 hσ)⟩
  | @EqTm0.pathBeta _ Ψ Φ Γ t r T h0 => ⟨(sub_ty hS h0).1, fun {Ψ' Φ' Δ σ τ} hσ =>
    by simp only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil]; exact EqTm0.pathBeta (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil] using (sub_ty hS h0).2.1 hσ)⟩
  | @EqTm0.pathEta _ Ψ Φ Γ A a b p h0 => ⟨(sub_ty hS h0).1, fun {Ψ' Φ' Δ σ τ} hσ =>
    by simp only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil]; exact EqTm0.pathEta (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil] using (sub_ty hS h0).2.1 hσ)⟩
  | @EqTm0.ipiEta _ Ψ Φ Γ A p h0 => ⟨(sub_ty hS h0).1, fun {Ψ' Φ' Δ σ τ} hσ =>
    by simp only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil]; exact EqTm0.ipiEta (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil] using (sub_ty hS h0).2.1 hσ)⟩
  | @EqTm0.pathZero _ Ψ Φ Γ A a b p h0 => ⟨(sub_ty hS h0).1, fun {Ψ' Φ' Δ σ τ} hσ =>
    by simp only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil]; exact EqTm0.pathZero (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil] using (sub_ty hS h0).2.1 hσ)⟩
  | @EqTm0.pathOne _ Ψ Φ Γ A a b p h0 => ⟨(sub_ty hS h0).1, fun {Ψ' Φ' Δ σ τ} hσ =>
    by simp only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil]; exact EqTm0.pathOne (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil] using (sub_ty hS h0).2.1 hσ)⟩
  | @EqTm0.splitL _ Ψ Φ Γ φ ψ t u T h0 h1 => ⟨(sub_ty hS h1).1, fun {Ψ' Φ' Δ σ τ} hσ =>
    by simp only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil]; exact EqTm0.splitL (ent_trans hσ.ent (ent_subst h0 _)) (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil] using (sub_ty hS h1).2.1 hσ)⟩
  | @EqTm0.splitR _ Ψ Φ Γ φ ψ t u T h0 h1 => ⟨(sub_ty hS h1).1, fun {Ψ' Φ' Δ σ τ} hσ =>
    by simp only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil]; exact EqTm0.splitR (ent_trans hσ.ent (ent_subst h0 _)) (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil] using (sub_ty hS h1).2.1 hσ)⟩
  | @EqTm0.transpFace _ Ψ Φ Γ A φ a T h0 h1 => ⟨(sub_ty hS h1).1, fun {Ψ' Φ' Δ σ τ} hσ =>
    by simp only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil]; exact EqTm0.transpFace (ent_trans hσ.ent (ent_subst h0 _)) (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil] using (sub_ty hS h1).2.1 hσ)⟩
  | @EqTm0.hcompFace _ Ψ Φ Γ A φ u a T h0 h1 => ⟨(sub_ty hS h1).1, fun {Ψ' Φ' Δ σ τ} hσ =>
    by simp only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil]; exact EqTm0.hcompFace (ent_trans hσ.ent (ent_subst h0 _)) (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil] using (sub_ty hS h1).2.1 hσ)⟩
  | @EqTm0.transpU _ Ψ Φ Γ l φ a T h0 => ⟨(sub_ty hS h0).1, fun {Ψ' Φ' Δ σ τ} hσ =>
    by simp only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil]; exact EqTm0.transpU (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil] using (sub_ty hS h0).2.1 hσ)⟩
  | @EqTm0.transpPi _ Ψ Φ Γ A B φ u0 T h0 => ⟨(sub_ty hS h0).1, fun {Ψ' Φ' Δ σ τ} hσ =>
    by rw [transpPi_subst]; simp only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil]; exact EqTm0.transpPi (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil] using (sub_ty hS h0).2.1 hσ)⟩
  | @EqTm0.transpSigma _ Ψ Φ Γ A B φ u0 T h0 => ⟨(sub_ty hS h0).1, fun {Ψ' Φ' Δ σ τ} hσ =>
    by rw [transpSigma_subst]; simp only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil]; exact EqTm0.transpSigma (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil] using (sub_ty hS h0).2.1 hσ)⟩
  | @EqTm0.transpPath _ Ψ Φ Γ A a b φ p0 T h0 => ⟨(sub_ty hS h0).1, fun {Ψ' Φ' Δ σ τ} hσ =>
    by rw [transpPath_subst]; simp only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil]; exact EqTm0.transpPath (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil] using (sub_ty hS h0).2.1 hσ)⟩
  | @EqTm0.transpGlue _ Ψ Φ Γ A φ T' e ψ u0 T l δ h0 h1 h2 h3 h4 => ⟨(sub_ty hS h0).1, fun {Ψ' Φ' Δ σ τ} hσ =>
    by
      have hφ := scoped_cof_right (scoped_of_ty h2)
      rw [transpGlueWith_subst]; simp only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil]
      exact EqTm0.transpGlue (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil] using (sub_ty hS h0).2.1 hσ) ((sub_ty hS h1).2.1 (hσ.dup hS)) (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil] using (sub_ty hS h2).2.1 ((hσ.dup hS).underCof hφ))
        (ent_trans (ent_subst h3 _) (forall0_subst _ τ).1)
        (ent_trans (forall0_subst _ τ).2 (ent_subst h4 _))⟩
  | @EqTm0.transpIPi _ Ψ Φ Γ A φ u0 T h0 => ⟨(sub_ty hS h0).1, fun {Ψ' Φ' Δ σ τ} hσ =>
    by rw [transpIPi_subst]; simp only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil]; exact EqTm0.transpIPi (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil] using (sub_ty hS h0).2.1 hσ)⟩
  | @EqTm0.hcompIPi _ Ψ Φ Γ A φ u u0 T h0 => ⟨(sub_ty hS h0).1, fun {Ψ' Φ' Δ σ τ} hσ =>
    by rw [hcompIPi_subst]; simp only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil]; exact EqTm0.hcompIPi (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil] using (sub_ty hS h0).2.1 hσ)⟩
  | @EqTm0.hcompPi _ Ψ Φ Γ A B φ u u0 T h0 => ⟨(sub_ty hS h0).1, fun {Ψ' Φ' Δ σ τ} hσ =>
    by rw [hcompPi_subst]; simp only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil]; exact EqTm0.hcompPi (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil] using (sub_ty hS h0).2.1 hσ)⟩
  | @EqTm0.hcompSigma _ Ψ Φ Γ A B φ u u0 T h0 => ⟨(sub_ty hS h0).1, fun {Ψ' Φ' Δ σ τ} hσ =>
    by rw [hcompSigma_subst]; simp only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil]; exact EqTm0.hcompSigma (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil] using (sub_ty hS h0).2.1 hσ)⟩
  | @EqTm0.hcompPath _ Ψ Φ Γ A a b φ u p0 T h0 => ⟨(sub_ty hS h0).1, fun {Ψ' Φ' Δ σ τ} hσ =>
    by rw [hcompPath_subst]; simp only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil]; exact EqTm0.hcompPath (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil] using (sub_ty hS h0).2.1 hσ)⟩
  | @EqTm0.hcompGlue _ Ψ Φ Γ A φ T' e ψ u u0 T l h0 h1 h2 => ⟨(sub_ty hS h0).1, fun {Ψ' Φ' Δ σ τ} hσ =>
    by have hφ := scoped_cof_right (scoped_of_ty h2); rw [hcompGlue_subst]; simp only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil]; exact EqTm0.hcompGlue (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil] using (sub_ty hS h0).2.1 hσ) ((sub_ty hS h1).2.1 hσ) (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil] using (sub_ty hS h2).2.1 (hσ.underCof hφ))⟩
  | @EqTm0.hcompU _ Ψ Φ Γ φ u u0 T l h0 => ⟨(sub_ty hS h0).1, fun {Ψ' Φ' Δ σ τ} hσ =>
    by rw [hcompU_subst]; simp only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil]; exact EqTm0.hcompU (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil] using (sub_ty hS h0).2.1 hσ)⟩
  | @EqTm0.glueFace _ Ψ Φ Γ A φ T e G h0 h1 => ⟨(sub_ty hS h1).1, fun {Ψ' Φ' Δ σ τ} hσ =>
    by simp only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil]; exact EqTm0.glueFace (ent_trans hσ.ent (ent_subst h0 _)) (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil] using (sub_ty hS h1).2.1 hσ)⟩
  | @EqTm0.glueElFace _ Ψ Φ Γ φ e t a G h0 h1 => ⟨(sub_ty hS h1).1, fun {Ψ' Φ' Δ σ τ} hσ =>
    by simp only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil]; exact EqTm0.glueElFace (ent_trans hσ.ent (ent_subst h0 _)) (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil] using (sub_ty hS h1).2.1 hσ)⟩
  | @EqTm0.unglueFace _ Ψ Φ Γ A φ T e g l h0 h1 h2 h3 => ⟨(sub_ty hS h1).1, fun {Ψ' Φ' Δ σ τ} hσ =>
    by simp only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil]; exact EqTm0.unglueFace (ent_trans hσ.ent (ent_subst h0 _)) (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil] using (sub_ty hS h1).2.1 hσ) ((sub_ty hS h2).2.1 hσ) (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil] using (sub_ty hS h3).2.1 hσ)⟩
  | @EqTm0.glueBeta _ Ψ Φ Γ φ e t a G h0 h1 => ⟨(sub_ty hS h0).1, fun {Ψ' Φ' Δ σ τ} hσ =>
    by simp only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil]; exact EqTm0.glueBeta (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil] using (sub_ty hS h0).2.1 hσ) (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil] using (sub_ty hS h1).2.1 hσ)⟩
  | @EqTm0.glueEta _ Ψ Φ Γ A φ T e g h0 => ⟨(sub_ty hS h0).1, fun {Ψ' Φ' Δ σ τ} hσ =>
    by simp only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil]; exact EqTm0.glueEta (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil] using (sub_ty hS h0).2.1 hσ)⟩
  | @EqTm0.data _ Ψ Φ Γ d D ps ps' h0 h1 h2 h3 => ⟨(sub_ty hS h1).1, fun {Ψ' Φ' Δ σ τ} hσ =>
    by simp only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil]; exact EqTm0.data h0 ((sub_ty hS h1).2.1 hσ) ((sub_ty hS h2).2.1 hσ) ((sub_eqtele hS h3).2 (fun k A hk => by simpa using hS.params _ _ _ _ h0 hk) hσ)⟩
  | @EqTm0.con _ Ψ Φ Γ d D c C ps ps' args args' rs rs' h0 h1 h2 h3 h4 h5 h6 h7 => ⟨(sub_ty hS h2).1, fun {Ψ' Φ' Δ σ τ} hσ =>
    by
      obtain ⟨D', C', hD', hC', hps, hlen, _, _⟩ := gen_con h2 rfl
      rw [h0] at hD'; cases hD'; rw [h1] at hC'; cases hC'
      have ht := (sub_eqtele hS h5).2 (fun k A hk => by
        rw [List.length_reverse, hlen]; exact argTys_closed hS h0 h1 k A hk) hσ
      simp only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil]
      refine EqTm0.con h0 h1 (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil] using (sub_ty hS h2).2.1 hσ) (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil] using (sub_ty hS h3).2.1 hσ) ((sub_eqtele hS h4).2 (fun k A hk => by simpa using hS.params _ _ _ _ h0 hk) hσ) ?_ (by simpa using h6) ?_
      · rw [toList_subst hps, ← List.map_reverse]; exact ht
      · intro k r r' hr hr'
        rw [List.getElem?_map] at hr hr'
        obtain ⟨r0, hr0, rfl⟩ := Option.map_eq_some_iff.1 hr
        obtain ⟨r0', hr0', rfl⟩ := Option.map_eq_some_iff.1 hr'
        exact I_eq_subst (h7 k r0 r0' hr0 hr0') _⟩
  | @EqTm0.elim _ Ψ Φ Γ d D ps ps' P P' bs bs' t t' m h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 => ⟨(sub_ty hS h1).1, fun {Ψ' Φ' Δ σ τ} hσ =>
    by
      obtain ⟨D', hD', hps, hlen, _⟩ := gen_elim h1 rfl
      rw [h0] at hD'; cases hD'
      simp only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil]
      refine EqTm0.elim h0 (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil] using (sub_ty hS h1).2.1 hσ) (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil] using (sub_ty hS h2).2.1 hσ) ((sub_eqtele hS h3).2 (fun k A hk => by simpa using hS.params _ _ _ _ h0 hk) hσ)
        ((sub_eq hS h4).2 (hσ.upC hS (sub_eq hS h4).1)) (isList_subst h5 _ _) (isList_subst h6 _ _)
        (by rw [toList_subst h5, toList_subst h6, List.length_map, List.length_map, h7]) ?_ ((sub_eq hS h9).2 hσ)
      intro c C b b' hc hb hb'
      rw [toList_subst h5, List.getElem?_map] at hb
      rw [toList_subst h6, List.getElem?_map] at hb'
      obtain ⟨b0, hb0, rfl⟩ := Option.map_eq_some_iff.1 hb
      obtain ⟨b0', hb0', rfl⟩ := Option.map_eq_some_iff.1 hb'
      have := (sub_eq hS (h8 c C b0 b0' hc hb0 hb0')).2 hσ
      rwa [branchTy_subst _ _ hS h0 hc hps hlen] at this⟩
  | @EqTm0.conBnd _ Ψ Φ Γ d D c C ps args rs k ψ b T h0 h1 h2 h3 h4 h5 h6 => ⟨(sub_ty hS h6).1, fun {Ψ' Φ' Δ σ τ} hσ =>
    by
      obtain ⟨D', C', hD', hC', _, hlen, hlena, hlenr⟩ := gen_con h6 rfl
      rw [h0] at hD'; cases hD'; rw [h1] at hC'; cases hC'
      have hb := hS.bnd _ _ _ _ _ _ _ h0 h1 h2
      rw [bndAt_subst _ _ (by rw [hlen, hlena, hlenr]; exact hb.2), ← toList_subst h4, ← toList_subst h5]
      exact EqTm0.conBnd h0 h1 h2 (by
          have := ent_trans hσ.ent (ent_subst h3 τ); rwa [cofAt_subst _ (by rw [hlenr]; exact hb.1)] at this)
        (isList_subst h4 _ _) (isList_subst h5 _ _) ((sub_ty hS h6).2.1 hσ)⟩
  | @EqTm0.elimCon _ Ψ Φ Γ d D c C ps P bs b qs args rs T h0 h1 h2 h3 h4 h5 h6 h7 => ⟨(sub_tele hS h6).1, fun {Ψ' Φ' Δ σ τ} hσ =>
    by
      obtain ⟨D', hD', _, hlen, _⟩ := gen_elim h7 rfl
      rw [h0] at hD'; cases hD'
      have ht := ((sub_tele hS h6).2 (fun k A hk => by rw [List.length_reverse, hlen]; exact argTys_closed hS h0 h1 k A hk)).1 hσ
      rw [elimCon_subst h4]; simp only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil]
      refine EqTm0.elimCon h0 h1 ?_ (isList_subst h3 _ _) (isList_subst h4 _ _) (isList_subst h5 _ _) ?_ (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil] using (sub_ty hS h7).2.1 hσ)
      · rw [toList_subst h5, List.getElem?_map, h2]; rfl
      · rw [toList_subst h3, ← List.map_reverse]; exact ht⟩
  | @EqTm0.elimHcomp _ Ψ Φ Γ d D ps P bs qs φ u a T h0 h1 h2 => ⟨(sub_ty hS h1).1, fun {Ψ' Φ' Δ σ τ} hσ =>
    by rw [elimHcomp_subst]; simp only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil]; exact EqTm0.elimHcomp h0 (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil] using (sub_ty hS h1).2.1 hσ) (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil] using (sub_ty hS h2).2.1 hσ)⟩
  | @EqTm0.transpData0 _ Ψ Φ Γ d D ps φ a T h0 h1 h2 => ⟨(sub_ty hS h2).1, fun {Ψ' Φ' Δ σ τ} hσ =>
    by simp only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil]; exact EqTm0.transpData0 h0 h1 (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil] using (sub_ty hS h2).2.1 hσ)⟩
  | @EqTm0.transpCon _ Ψ Φ Γ d D c C ps φ qs args rs T h0 h1 h2 h3 h4 h5 h6 => ⟨(sub_tele hS h5).1, fun {Ψ' Φ' Δ σ τ} hσ =>
    by
      obtain ⟨D', hD', hlen0⟩ := gen_transp_data h6 rfl
      rw [h0] at hD'; cases hD'
      have hlen := hlen0
      rw [← List.length_map (f := (·.dinst .zero)), ← dinst_toList h3] at hlen
      have ht := ((sub_tele hS h5).2 (fun k A hk => by rw [List.length_reverse, hlen]; exact argTys_closed hS h0 h2 k A hk)).1 hσ
      rw [transpCon_subst hS h0 h2 h3 h4 hlen0]; simp only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil]
      refine EqTm0.transpCon h0 h1 h2 (isList_subst h3 _ _) (isList_subst h4 _ _) ?_ (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil] using (sub_ty hS h6).2.1 hσ)
      rw [dinst_toList (isList_subst h3 _ _), toList_subst h3]
      rw [dinst_toList h3] at ht
      simpa only [List.map_reverse, List.map_map, Function.comp_def, dinst_subst, I.subst, Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil] using ht⟩
  | @EqTm0.transpHcomp _ Ψ Φ Γ d D ps φ qs ψ u a T h0 h1 h2 h3 => ⟨(sub_ty hS h2).1, fun {Ψ' Φ' Δ σ τ} hσ =>
    by rw [transpHcomp_subst]; simp only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil]; exact EqTm0.transpHcomp h0 h1 (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil] using (sub_ty hS h2).2.1 hσ) (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil] using (sub_ty hS h3).2.1 hσ)⟩
end

end KubusCore.Meta
