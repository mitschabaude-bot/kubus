import KubusCore.Meta.RenLemmas

/-!
# Metatheory: renaming is admissible

`ren_ty`/`ren_eq`: the minimal judgments are closed under renaming term variables arbitrarily
and interval variables injectively (`TyRen`), in particular under weakening by a term variable
(`HasTy.wk`) or an interval variable (`HasTy.dwk`). The signature must be closed (`SigClosed`,
implied by `WfSig`). Every derivation also yields `CtxRen` for its context, which provides the
well-formedness of the renamed context under binders.
-/

set_option maxHeartbeats 1000000

namespace KubusCore.Meta

open Tm

variable {S : Sig}

theorem rS_up_zero (ρ : Nat → Nat) : rS (upRen ρ) 0 = .var 0 := rfl
theorem rI_up_zero (δ : Nat → Nat) : rI (upRen δ) 0 = .var 0 := rfl

theorem argTys_closed (hS : SigClosed S) {d : Nat} {D : DataDecl} {c : Nat} {C : Ctor}
    (hd : S[d]? = some (.data D)) (hc : D.ctors[c]? = some C) (k : Nat) (A : Tm)
    (hk : (C.argTys d D.params.length)[k]? = some A) : A.closedB (D.params.length + k) 0 = true := by
  simp only [Ctor.argTys, List.getElem?_map] at hk
  obtain ⟨k', hk', rfl⟩ := Option.map_eq_some_iff.1 hk
  have : k' = k := by
    have := List.getElem?_eq_some_iff.1 hk'
    simp only [List.getElem_range] at this; exact this.2.symm
  subst this
  exact argTy_closed hS hd hc k'

theorem rn_lift (m : Nat) {k : Nat} {ρ : Nat → Nat} : rS (upRenN k ρ) = dupN m (upN k (rS ρ)) := by
  rw [upN_rS, dupN_rS]

mutual

theorem ren_wf (hS : SigClosed S) {Ψ Φ Γ} : Wf0 S Ψ Φ Γ → CtxRen S Ψ Φ Γ
  | .nil _ => trivial
  | .cons h0 => ⟨(ren_ty hS h0).1, fun _ _ _ _ _ hR => ⟨_, (ren_ty hS h0).2 hR⟩⟩

theorem ren_ty (hS : SigClosed S) {Ψ Φ Γ t A} : HasTy0 S Ψ Φ Γ t A → CtxRen S Ψ Φ Γ ∧
    ∀ {Ψ' Φ' Δ ρ δ}, TyRen S Ψ Φ Γ Ψ' Φ' Δ ρ δ →
      HasTy0 S Ψ' Φ' Δ (t.subst (rS ρ) (rI δ)) (A.subst (rS ρ) (rI δ))
  | .var h0 h1 => ⟨ren_wf hS h0, fun {Ψ' Φ' Δ ρ δ} hR =>
    by simp only [Tm.subst, rS]; exact HasTy0.var (hR.wf.wf hR.hscoped) (hR.look _ _ h1)⟩
  | .conv h0 h1 => ⟨(ren_ty hS h0).1, fun {Ψ' Φ' Δ ρ δ} hR =>
    HasTy0.conv ((ren_ty hS h0).2 hR) ((ren_eq hS h1).2 hR)⟩
  | .restrict h0 h1 h2 => ⟨CtxRen.restrict h1 (ren_ty hS h2).1, fun {Ψ' Φ' Δ ρ δ} hR =>
    (ren_ty hS h2).2 (hR.restrict hR.hscoped (ent_refl _) (ent_trans hR.ent (ent_subst h1 _)))⟩
  | .const h0 h1 => ⟨ren_wf hS h0, fun {Ψ' Φ' Δ ρ δ} hR =>
    by obtain ⟨_, hA⟩ := hS.defn _ _ _ h1; rw [closed_subst_id hA (fun _ h => absurd h (Nat.not_lt_zero _)) (fun _ h => absurd h (Nat.not_lt_zero _))]; exact HasTy0.const (hR.wf.wf hR.hscoped) h1⟩
  | .univ h0 h1 => ⟨ren_wf hS h1, fun {Ψ' Φ' Δ ρ δ} hR =>
    HasTy0.univ h0 (hR.wf.wf hR.hscoped)⟩
  | .cumul h0 h1 => ⟨(ren_ty hS h1).1, fun {Ψ' Φ' Δ ρ δ} hR =>
    HasTy0.cumul h0 ((ren_ty hS h1).2 hR)⟩
  | .pi h0 h1 => ⟨(ren_ty hS h0).1, fun {Ψ' Φ' Δ ρ δ} hR =>
    by simp only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil]; exact HasTy0.pi ((ren_ty hS h0).2 hR) ((ren_ty hS h1).2 (hR.up (ren_ty hS h1).1))⟩
  | .lam h0 h1 => ⟨(ren_ty hS h0).1, fun {Ψ' Φ' Δ ρ δ} hR =>
    by simp only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil]; exact HasTy0.lam (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil] using (ren_ty hS h0).2 hR) ((ren_ty hS h1).2 (hR.up (ren_ty hS h1).1))⟩
  | .app h0 h1 => ⟨(ren_ty hS h0).1, fun {Ψ' Φ' Δ ρ δ} hR =>
    by simp only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil]; exact HasTy0.app (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil] using (ren_ty hS h0).2 hR) ((ren_ty hS h1).2 hR)⟩
  | .sigma h0 h1 => ⟨(ren_ty hS h0).1, fun {Ψ' Φ' Δ ρ δ} hR =>
    by simp only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil]; exact HasTy0.sigma ((ren_ty hS h0).2 hR) ((ren_ty hS h1).2 (hR.up (ren_ty hS h1).1))⟩
  | .pair h0 h1 h2 => ⟨(ren_ty hS h0).1, fun {Ψ' Φ' Δ ρ δ} hR =>
    by simp only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil]; exact HasTy0.pair (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil] using (ren_ty hS h0).2 hR) ((ren_ty hS h1).2 hR) (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil] using (ren_ty hS h2).2 hR)⟩
  | .fst h0 => ⟨(ren_ty hS h0).1, fun {Ψ' Φ' Δ ρ δ} hR =>
    by simp only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil]; exact HasTy0.fst (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil] using (ren_ty hS h0).2 hR)⟩
  | .snd h0 => ⟨(ren_ty hS h0).1, fun {Ψ' Φ' Δ ρ δ} hR =>
    by simp only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil]; exact HasTy0.snd (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil] using (ren_ty hS h0).2 hR)⟩
  | .path h0 h1 h2 => ⟨(ren_ty hS h1).1, fun {Ψ' Φ' Δ ρ δ} hR =>
    by simp only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil]; exact HasTy0.path ((ren_ty hS h0).2 hR.dup) (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil] using (ren_ty hS h1).2 hR) (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil] using (ren_ty hS h2).2 hR)⟩
  | .plam h0 h1 h2 h3 => ⟨(ren_ty hS h0).1, fun {Ψ' Φ' Δ ρ δ} hR =>
    by simp only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil]; exact HasTy0.plam (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil] using (ren_ty hS h0).2 hR) ((ren_ty hS h1).2 hR.dup) (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil] using (ren_eq hS h2).2 hR) (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil] using (ren_eq hS h3).2 hR)⟩
  | .papp h0 h1 => ⟨(ren_ty hS h0).1, fun {Ψ' Φ' Δ ρ δ} hR =>
    by simp only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil]; exact HasTy0.papp (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil] using (ren_ty hS h0).2 hR) (hR.sc h1)⟩
  | .ipi h0 h1 => ⟨ren_wf hS h0, fun {Ψ' Φ' Δ ρ δ} hR =>
    by simp only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil]; exact HasTy0.ipi (hR.wf.wf hR.hscoped) ((ren_ty hS h1).2 hR.dup)⟩
  | .ilam h0 h1 => ⟨(ren_ty hS h0).1, fun {Ψ' Φ' Δ ρ δ} hR =>
    by simp only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil]; exact HasTy0.ilam (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil] using (ren_ty hS h0).2 hR) ((ren_ty hS h1).2 hR.dup)⟩
  | .iapp h0 h1 => ⟨(ren_ty hS h0).1, fun {Ψ' Φ' Δ ρ δ} hR =>
    by simp only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil]; exact HasTy0.iapp (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil] using (ren_ty hS h0).2 hR) (hR.sc h1)⟩
  | .split h0 h1 h2 h3 h4 h5 h6 => ⟨(ren_ty hS h3).1, fun {Ψ' Φ' Δ ρ δ} hR =>
    by simp only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil]; exact HasTy0.split (hR.sc h0) (hR.sc h1) (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil] using (ent_trans hR.ent (ent_subst h2 _))) ((ren_ty hS h3).2 hR) ((ren_ty hS h4).2 (hR.underCof h0)) ((ren_ty hS h5).2 (hR.underCof h1)) ((ren_eq hS h6).2 ((hR.underCof h0).underCof h1))⟩
  | .abort h0 h1 => ⟨(ren_ty hS h1).1, fun {Ψ' Φ' Δ ρ δ} hR =>
    HasTy0.abort (ent_trans hR.ent (ent_subst h0 _)) ((ren_ty hS h1).2 hR)⟩
  | .transp h0 h1 h2 h3 => ⟨(ren_ty hS h3).1, fun {Ψ' Φ' Δ ρ δ} hR =>
    by simp only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil]; exact HasTy0.transp ((ren_ty hS h0).2 hR.dup) (hR.sc h1) (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil] using (ren_eq hS h2).2 (hR.underCof h1).dup) (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil] using (ren_ty hS h3).2 hR)⟩
  | .hcomp h0 h1 h2 h3 h4 => ⟨(ren_ty hS h0).1, fun {Ψ' Φ' Δ ρ δ} hR =>
    by simp only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil]; exact HasTy0.hcomp ((ren_ty hS h0).2 hR) (hR.sc h1) (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil] using (ren_ty hS h2).2 (hR.underCof h1).dup) ((ren_ty hS h3).2 hR) (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil] using (ren_eq hS h4).2 (hR.underCof h1))⟩
  | .glue h0 h1 h2 h3 => ⟨(ren_ty hS h0).1, fun {Ψ' Φ' Δ ρ δ} hR =>
    by simp only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil]; exact HasTy0.glue ((ren_ty hS h0).2 hR) (hR.sc h1) ((ren_ty hS h2).2 (hR.underCof h1)) (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil] using (ren_ty hS h3).2 (hR.underCof h1))⟩
  | .glueEl h0 h1 h2 h3 h4 => ⟨(ren_ty hS h0).1, fun {Ψ' Φ' Δ ρ δ} hR =>
    by have hφ := scoped_cof_right (scoped_of_ty h1); simp only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil]; exact HasTy0.glueEl (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil] using (ren_ty hS h0).2 hR) (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil] using (ren_ty hS h1).2 (hR.underCof hφ)) ((ren_ty hS h2).2 (hR.underCof hφ)) ((ren_ty hS h3).2 hR) (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil] using (ren_eq hS h4).2 (hR.underCof hφ))⟩
  | .unglue h0 h1 h2 h3 => ⟨(ren_ty hS h0).1, fun {Ψ' Φ' Δ ρ δ} hR =>
    by have hφ := scoped_cof_right (scoped_of_ty h2); simp only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil]; exact HasTy0.unglue (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil] using (ren_ty hS h0).2 hR) ((ren_ty hS h1).2 hR) (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil] using (ren_ty hS h2).2 (hR.underCof hφ)) (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil] using (ren_ty hS h3).2 hR)⟩
  | .data h0 h1 h2 => ⟨(ren_tele hS h2).1, fun {Ψ' Φ' Δ ρ δ} hR =>
    by simp only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil]; exact HasTy0.data h0 h1 ((ren_tele hS h2).2 (fun k A hk => by simpa using hS.params _ _ _ _ h0 hk) hR)⟩
  | .con h0 h1 h2 h3 h4 h5 h6 h7 => ⟨(ren_ty hS h3).1, fun {Ψ' Φ' Δ ρ δ} hR =>
    by
      have hlen := tele_length h4
      have ht := (ren_tele hS h5).2 (fun k A hk => by
        rw [List.length_reverse, hlen]; exact argTys_closed hS h0 h1 k A hk) hR
      simp only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil]
      refine HasTy0.con h0 h1 (isList_subst h2 _ _) ((ren_ty hS h3).2 hR)
        ((ren_tele hS h4).2 (fun k A hk => by simpa using hS.params _ _ _ _ h0 hk) hR) ?_ (by simpa using h6) (fun r hr => ?_)
      · rw [toList_subst h2, ← List.map_reverse]; exact ht
      · obtain ⟨r0, hr0, rfl⟩ := List.mem_map.1 hr; exact hR.sc (h7 r0 hr0)⟩
  | .elim h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 => ⟨(ren_ty hS h2).1, fun {Ψ' Φ' Δ ρ δ} hR =>
    by
      have hlen := tele_length h3
      simp only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil]
      refine HasTy0.elim h0 (isList_subst h1 _ _) ((ren_ty hS h2).2 hR)
        ((ren_tele hS h3).2 (fun k A hk => by simpa using hS.params _ _ _ _ h0 hk) hR)
        ((ren_ty hS h4).2 (hR.up (ren_ty hS h4).1)) (isList_subst h5 _ _)
        (by rw [toList_subst h5, List.length_map, h6]) ?_ ?_ ((ren_ty hS h9).2 hR)
      · intro c C b hc hb
        rw [toList_subst h5, List.getElem?_map] at hb
        obtain ⟨b0, hb0, rfl⟩ := Option.map_eq_some_iff.1 hb
        have := (ren_ty hS (h7 c C b0 hc hb0)).2 hR
        rwa [branchTy_subst _ _ hS h0 hc h1 hlen, up_rS] at this
      · intro c C b k ψ e hc hb hk
        rw [toList_subst h5, List.getElem?_map] at hb
        obtain ⟨b0, hb0, rfl⟩ := Option.map_eq_some_iff.1 hb
        have hψ := hS.bnd _ _ _ _ _ _ _ h0 hc hk
        have := (ren_eq hS (h8 c C b0 k ψ e hc hb0 hk)).2
          (hR.branch hS h0 hc h1 hlen hψ.1 (ren_eq hS (h8 c C b0 k ψ e hc hb0 hk)).1)
        rw [rn_lift C.dims, ← IupN_rI, branchApp_subst, bndElim_subst _ _ h1 hlen h5 e hψ.2,
          branchBody_subst, up_rS] at this
        exact this⟩

theorem ren_tele (hS : SigClosed S) {Ψ Φ Γ ts Δt prev} : HasTele0 S Ψ Φ Γ ts Δt prev →
    CtxRen S Ψ Φ Γ ∧ ((∀ (k : Nat) (A : Tm), Δt[k]? = some A → A.closedB (prev.length + k) 0 = true) →
    ∀ {Ψ' Φ' Δ ρ δ}, TyRen S Ψ Φ Γ Ψ' Φ' Δ ρ δ →
      HasTele0 S Ψ' Φ' Δ (ts.subst (rS ρ) (rI δ)) Δt (prev.map (·.subst (rS ρ) (rI δ))))
  | .nil h0 => ⟨ren_wf hS h0,
    fun _ => fun hR => HasTele0.nil (hR.wf.wf hR.hscoped)⟩
  | .cons h0 h1 => ⟨(ren_ty hS h0).1,
    fun hcl => fun hR => by
      have hA := hcl 0 _ List.getElem?_cons_zero
      rw [Nat.add_zero] at hA
      have := (ren_ty hS h0).2 hR
      rw [substList_subst hA] at this
      exact HasTele0.cons this ((ren_tele hS h1).2 (fun k B hk => by
        have := hcl (k + 1) B hk; simpa [Nat.add_assoc, Nat.add_comm 1] using this) hR)⟩

theorem ren_eqtele (hS : SigClosed S) {Ψ Φ Γ ts ts' Δt prev} : EqTele0 S Ψ Φ Γ ts ts' Δt prev →
    CtxRen S Ψ Φ Γ ∧ ((∀ (k : Nat) (A : Tm), Δt[k]? = some A → A.closedB (prev.length + k) 0 = true) →
    ∀ {Ψ' Φ' Δ ρ δ}, TyRen S Ψ Φ Γ Ψ' Φ' Δ ρ δ →
      EqTele0 S Ψ' Φ' Δ (ts.subst (rS ρ) (rI δ)) (ts'.subst (rS ρ) (rI δ)) Δt (prev.map (·.subst (rS ρ) (rI δ))))
  | .nil h0 => ⟨ren_wf hS h0,
    fun _ => fun hR => EqTele0.nil (hR.wf.wf hR.hscoped)⟩
  | .cons h0 h1 => ⟨(ren_eq hS h0).1,
    fun hcl => fun hR => by
      have hA := hcl 0 _ List.getElem?_cons_zero
      rw [Nat.add_zero] at hA
      have := (ren_eq hS h0).2 hR
      rw [substList_subst hA] at this
      exact EqTele0.cons this ((ren_eqtele hS h1).2 (fun k B hk => by
        have := hcl (k + 1) B hk; simpa [Nat.add_assoc, Nat.add_comm 1] using this) hR)⟩
  | .dataInj h0 h1 h2 h3 => ⟨(ren_tele hS h1).1,
    fun _ => fun hR => by simp only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil]; exact EqTele0.dataInj h0 ((ren_tele hS h1).2 (fun k A hk => by simpa using hS.params _ _ _ _ h0 hk) hR) ((ren_tele hS h2).2 (fun k A hk => by simpa using hS.params _ _ _ _ h0 hk) hR) (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil] using (ren_eq hS h3).2 hR)⟩

theorem ren_eq (hS : SigClosed S) {Ψ Φ Γ t u A} : EqTm0 S Ψ Φ Γ t u A → CtxRen S Ψ Φ Γ ∧
    ∀ {Ψ' Φ' Δ ρ δ}, TyRen S Ψ Φ Γ Ψ' Φ' Δ ρ δ →
      EqTm0 S Ψ' Φ' Δ (t.subst (rS ρ) (rI δ)) (u.subst (rS ρ) (rI δ)) (A.subst (rS ρ) (rI δ))
  | .refl h0 => ⟨(ren_ty hS h0).1, fun {Ψ' Φ' Δ ρ δ} hR =>
    EqTm0.refl ((ren_ty hS h0).2 hR)⟩
  | .symm h0 => ⟨(ren_eq hS h0).1, fun {Ψ' Φ' Δ ρ δ} hR =>
    EqTm0.symm ((ren_eq hS h0).2 hR)⟩
  | .trans h0 h1 => ⟨(ren_eq hS h0).1, fun {Ψ' Φ' Δ ρ δ} hR =>
    EqTm0.trans ((ren_eq hS h0).2 hR) ((ren_eq hS h1).2 hR)⟩
  | .conv h0 h1 => ⟨(ren_eq hS h0).1, fun {Ψ' Φ' Δ ρ δ} hR =>
    EqTm0.conv ((ren_eq hS h0).2 hR) ((ren_eq hS h1).2 hR)⟩
  | .restrict h0 h1 h2 => ⟨CtxRen.restrict h1 (ren_eq hS h2).1, fun {Ψ' Φ' Δ ρ δ} hR =>
    (ren_eq hS h2).2 (hR.restrict hR.hscoped (ent_refl _) (ent_trans hR.ent (ent_subst h1 _)))⟩
  | .cumul h0 h1 => ⟨(ren_eq hS h1).1, fun {Ψ' Φ' Δ ρ δ} hR =>
    EqTm0.cumul h0 ((ren_eq hS h1).2 hR)⟩
  | .delta h0 h1 => ⟨(ren_ty hS h0).1, fun {Ψ' Φ' Δ ρ δ} hR =>
    by
      obtain ⟨ht, hA⟩ := hS.defn _ _ _ h1
      have h00 : ∀ x, x < 0 → x < 0 := fun _ h => h
      rw [closed_subst_id hA (fun _ h => absurd h (Nat.not_lt_zero _)) (fun _ h => absurd h (Nat.not_lt_zero _)),
        closed_subst_id ht (fun _ h => absurd h (Nat.not_lt_zero _)) (fun _ h => absurd h (Nat.not_lt_zero _))]
      have := ((ren_ty hS h0).2 hR)
      rw [closed_subst_id hA (fun _ h => absurd h (Nat.not_lt_zero _)) (fun _ h => absurd h (Nat.not_lt_zero _))] at this
      exact EqTm0.delta this h1⟩
  | .absurd h0 h1 h2 => ⟨(ren_ty hS h1).1, fun {Ψ' Φ' Δ ρ δ} hR =>
    EqTm0.absurd (ent_trans hR.ent (ent_subst h0 _)) ((ren_ty hS h1).2 hR) ((ren_ty hS h2).2 hR)⟩
  | .local h0 h1 h2 h3 h4 h5 h6 => ⟨(ren_ty hS h3).1, fun {Ψ' Φ' Δ ρ δ} hR =>
    by exact EqTm0.local (hR.sc h0) (hR.sc h1) (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil] using (ent_trans hR.ent (ent_subst h2 _))) ((ren_ty hS h3).2 hR) ((ren_ty hS h4).2 hR) ((ren_eq hS h5).2 (hR.underCof h0)) ((ren_eq hS h6).2 (hR.underCof h1))⟩
  | .face h0 h1 h2 h3 => ⟨(ren_ty hS h2).1, fun {Ψ' Φ' Δ ρ δ} hR =>
    by rw [dset_rn hR.inj]; exact EqTm0.face (hR.bound _ h0) (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil] using (ent_trans hR.ent (ent_subst h1 _))) ((ren_ty hS h2).2 hR) ((ren_ty hS h3).2 hR)⟩
  | .faceU h0 h1 h2 => ⟨(ren_ty hS h2).1, fun {Ψ' Φ' Δ ρ δ} hR =>
    by rw [dset_rn hR.inj]; exact EqTm0.faceU (hR.bound _ h0) (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil] using (ent_trans hR.ent (ent_subst h1 _))) ((ren_ty hS h2).2 hR)⟩
  | .pi h0 h1 => ⟨(ren_eq hS h0).1, fun {Ψ' Φ' Δ ρ δ} hR =>
    by simp only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil]; exact EqTm0.pi ((ren_eq hS h0).2 hR) ((ren_eq hS h1).2 (hR.up (ren_eq hS h1).1))⟩
  | .lam h0 h1 => ⟨(ren_ty hS h0).1, fun {Ψ' Φ' Δ ρ δ} hR =>
    by simp only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil]; exact EqTm0.lam (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil] using (ren_ty hS h0).2 hR) ((ren_eq hS h1).2 (hR.up (ren_eq hS h1).1))⟩
  | .app h0 h1 => ⟨(ren_eq hS h0).1, fun {Ψ' Φ' Δ ρ δ} hR =>
    by simp only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil]; exact EqTm0.app (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil] using (ren_eq hS h0).2 hR) ((ren_eq hS h1).2 hR)⟩
  | .sigma h0 h1 => ⟨(ren_eq hS h0).1, fun {Ψ' Φ' Δ ρ δ} hR =>
    by simp only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil]; exact EqTm0.sigma ((ren_eq hS h0).2 hR) ((ren_eq hS h1).2 (hR.up (ren_eq hS h1).1))⟩
  | .pair h0 h1 h2 => ⟨(ren_ty hS h0).1, fun {Ψ' Φ' Δ ρ δ} hR =>
    by simp only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil]; exact EqTm0.pair (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil] using (ren_ty hS h0).2 hR) ((ren_eq hS h1).2 hR) (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil] using (ren_eq hS h2).2 hR)⟩
  | .fst h0 => ⟨(ren_eq hS h0).1, fun {Ψ' Φ' Δ ρ δ} hR =>
    by simp only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil]; exact EqTm0.fst (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil] using (ren_eq hS h0).2 hR)⟩
  | .snd h0 => ⟨(ren_eq hS h0).1, fun {Ψ' Φ' Δ ρ δ} hR =>
    by simp only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil]; exact EqTm0.snd (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil] using (ren_eq hS h0).2 hR)⟩
  | .path h0 h1 h2 => ⟨(ren_eq hS h1).1, fun {Ψ' Φ' Δ ρ δ} hR =>
    by simp only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil]; exact EqTm0.path ((ren_eq hS h0).2 hR.dup) (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil] using (ren_eq hS h1).2 hR) (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil] using (ren_eq hS h2).2 hR)⟩
  | .plam h0 h1 h2 h3 => ⟨(ren_ty hS h0).1, fun {Ψ' Φ' Δ ρ δ} hR =>
    by simp only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil]; exact EqTm0.plam (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil] using (ren_ty hS h0).2 hR) (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil] using (ren_ty hS h1).2 hR) (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil] using (ren_ty hS h2).2 hR) ((ren_eq hS h3).2 hR.dup)⟩
  | .papp h0 h1 h2 h3 => ⟨(ren_eq hS h0).1, fun {Ψ' Φ' Δ ρ δ} hR =>
    by simp only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil]; exact EqTm0.papp (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil] using (ren_eq hS h0).2 hR) (hR.sc h1) (hR.sc h2) (I_eq_subst h3 _)⟩
  | .split h0 h1 h2 h3 => ⟨(ren_ty hS h0).1, fun {Ψ' Φ' Δ ρ δ} hR =>
    by have hφ := scoped_cof_right (scoped_of_eq h2); have hψ := scoped_cof_right (scoped_of_eq h3); simp only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil]; exact EqTm0.split (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil] using (ren_ty hS h0).2 hR) (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil] using (ren_ty hS h1).2 hR) ((ren_eq hS h2).2 (hR.underCof hφ)) ((ren_eq hS h3).2 (hR.underCof hψ))⟩
  | .transp h0 h1 h2 h3 h4 h5 => ⟨(ren_ty hS h0).1, fun {Ψ' Φ' Δ ρ δ} hR =>
    by simp only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil]; exact EqTm0.transp (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil] using (ren_ty hS h0).2 hR) (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil] using (ren_ty hS h1).2 hR) ((ren_eq hS h2).2 hR.dup) (ent_subst h3 _) (ent_subst h4 _) (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil] using (ren_eq hS h5).2 hR)⟩
  | .hcomp h0 h1 h2 h3 h4 h5 h6 => ⟨(ren_ty hS h0).1, fun {Ψ' Φ' Δ ρ δ} hR =>
    by have hφ := scoped_cof_shift_right (scoped_of_eq h5); simp only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil]; exact EqTm0.hcomp (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil] using (ren_ty hS h0).2 hR) (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil] using (ren_ty hS h1).2 hR) ((ren_eq hS h2).2 hR) (ent_subst h3 _) (ent_subst h4 _) (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil] using (ren_eq hS h5).2 (hR.underCof hφ).dup) ((ren_eq hS h6).2 hR)⟩
  | .glue h0 h1 h2 h3 h4 h5 h6 => ⟨(ren_ty hS h0).1, fun {Ψ' Φ' Δ ρ δ} hR =>
    by have hφ := scoped_cof_right (scoped_of_eq h5); simp only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil]; exact EqTm0.glue (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil] using (ren_ty hS h0).2 hR) (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil] using (ren_ty hS h1).2 hR) ((ren_eq hS h2).2 hR) (ent_subst h3 _) (ent_subst h4 _) ((ren_eq hS h5).2 (hR.underCof hφ)) (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil] using (ren_eq hS h6).2 (hR.underCof hφ))⟩
  | .glueEl h0 h1 h2 h3 h4 h5 h6 => ⟨(ren_ty hS h0).1, fun {Ψ' Φ' Δ ρ δ} hR =>
    by have hφ := scoped_cof_right (scoped_of_eq h4); simp only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil]; exact EqTm0.glueEl (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil] using (ren_ty hS h0).2 hR) (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil] using (ren_ty hS h1).2 hR) (ent_subst h2 _) (ent_subst h3 _) (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil] using (ren_eq hS h4).2 (hR.underCof hφ)) ((ren_eq hS h5).2 (hR.underCof hφ)) ((ren_eq hS h6).2 hR)⟩
  | .unglue h0 h1 h2 h3 h4 h5 => ⟨(ren_ty hS h0).1, fun {Ψ' Φ' Δ ρ δ} hR =>
    by have hφ := scoped_cof_right (scoped_of_eq h4); simp only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil]; exact EqTm0.unglue (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil] using (ren_ty hS h0).2 hR) (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil] using (ren_ty hS h1).2 hR) (ent_subst h2 _) (ent_subst h3 _) (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil] using (ren_eq hS h4).2 (hR.underCof hφ)) (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil] using (ren_eq hS h5).2 hR)⟩
  | .ipi h0 h1 => ⟨ren_wf hS h0, fun {Ψ' Φ' Δ ρ δ} hR =>
    by simp only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil]; exact EqTm0.ipi (hR.wf.wf hR.hscoped) ((ren_eq hS h1).2 hR.dup)⟩
  | .ilam h0 h1 => ⟨(ren_ty hS h0).1, fun {Ψ' Φ' Δ ρ δ} hR =>
    by simp only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil]; exact EqTm0.ilam (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil] using (ren_ty hS h0).2 hR) ((ren_eq hS h1).2 hR.dup)⟩
  | .iapp h0 h1 h2 h3 => ⟨(ren_eq hS h0).1, fun {Ψ' Φ' Δ ρ δ} hR =>
    by simp only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil]; exact EqTm0.iapp (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil] using (ren_eq hS h0).2 hR) (hR.sc h1) (hR.sc h2) (I_eq_subst h3 _)⟩
  | .piInjDom h0 => ⟨(ren_eq hS h0).1, fun {Ψ' Φ' Δ ρ δ} hR =>
    by simp only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil]; exact EqTm0.piInjDom (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil] using (ren_eq hS h0).2 hR)⟩
  | .piInjCod h0 h1 => ⟨(ren_eq hS h0).1, fun {Ψ' Φ' Δ ρ δ} hR =>
    by simp only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil]; exact EqTm0.piInjCod (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil] using (ren_eq hS h0).2 hR) ((ren_ty hS h1).2 hR)⟩
  | .sigmaInjDom h0 => ⟨(ren_eq hS h0).1, fun {Ψ' Φ' Δ ρ δ} hR =>
    by simp only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil]; exact EqTm0.sigmaInjDom (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil] using (ren_eq hS h0).2 hR)⟩
  | .sigmaInjCod h0 h1 => ⟨(ren_eq hS h0).1, fun {Ψ' Φ' Δ ρ δ} hR =>
    by simp only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil]; exact EqTm0.sigmaInjCod (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil] using (ren_eq hS h0).2 hR) ((ren_ty hS h1).2 hR)⟩
  | .pathInjLine h0 h1 => ⟨(ren_eq hS h0).1, fun {Ψ' Φ' Δ ρ δ} hR =>
    by simp only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil]; exact EqTm0.pathInjLine (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil] using (ren_eq hS h0).2 hR) (hR.sc h1)⟩
  | .pathInjLeft h0 => ⟨(ren_eq hS h0).1, fun {Ψ' Φ' Δ ρ δ} hR =>
    by simp only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil]; exact EqTm0.pathInjLeft (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil] using (ren_eq hS h0).2 hR)⟩
  | .pathInjRight h0 => ⟨(ren_eq hS h0).1, fun {Ψ' Φ' Δ ρ δ} hR =>
    by simp only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil]; exact EqTm0.pathInjRight (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil] using (ren_eq hS h0).2 hR)⟩
  | .ipiInj h0 h1 => ⟨(ren_eq hS h0).1, fun {Ψ' Φ' Δ ρ δ} hR =>
    by simp only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil]; exact EqTm0.ipiInj (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil] using (ren_eq hS h0).2 hR) (hR.sc h1)⟩
  | .noConf h0 h1 h2 h3 => ⟨(ren_eq hS h1).1, fun {Ψ' Φ' Δ ρ δ} hR =>
    EqTm0.noConf (headClash_subst _ _ h0) ((ren_eq hS h1).2 hR) ((ren_ty hS h2).2 hR) ((ren_ty hS h3).2 hR)⟩
  | .piBeta h0 => ⟨(ren_ty hS h0).1, fun {Ψ' Φ' Δ ρ δ} hR =>
    by simp only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil]; exact EqTm0.piBeta (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil] using (ren_ty hS h0).2 hR)⟩
  | .piEta h0 => ⟨(ren_ty hS h0).1, fun {Ψ' Φ' Δ ρ δ} hR =>
    by simp only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil]; exact EqTm0.piEta (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil] using (ren_ty hS h0).2 hR)⟩
  | .fstBeta h0 => ⟨(ren_ty hS h0).1, fun {Ψ' Φ' Δ ρ δ} hR =>
    by simp only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil]; exact EqTm0.fstBeta (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil] using (ren_ty hS h0).2 hR)⟩
  | .sndBeta h0 => ⟨(ren_ty hS h0).1, fun {Ψ' Φ' Δ ρ δ} hR =>
    by simp only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil]; exact EqTm0.sndBeta (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil] using (ren_ty hS h0).2 hR)⟩
  | .sigmaEta h0 => ⟨(ren_ty hS h0).1, fun {Ψ' Φ' Δ ρ δ} hR =>
    by simp only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil]; exact EqTm0.sigmaEta (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil] using (ren_ty hS h0).2 hR)⟩
  | .pathBeta h0 => ⟨(ren_ty hS h0).1, fun {Ψ' Φ' Δ ρ δ} hR =>
    by simp only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil]; exact EqTm0.pathBeta (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil] using (ren_ty hS h0).2 hR)⟩
  | .pathEta h0 => ⟨(ren_ty hS h0).1, fun {Ψ' Φ' Δ ρ δ} hR =>
    by simp only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil]; exact EqTm0.pathEta (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil] using (ren_ty hS h0).2 hR)⟩
  | .ipiEta h0 => ⟨(ren_ty hS h0).1, fun {Ψ' Φ' Δ ρ δ} hR =>
    by simp only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil]; exact EqTm0.ipiEta (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil] using (ren_ty hS h0).2 hR)⟩
  | .pathZero h0 => ⟨(ren_ty hS h0).1, fun {Ψ' Φ' Δ ρ δ} hR =>
    by simp only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil]; exact EqTm0.pathZero (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil] using (ren_ty hS h0).2 hR)⟩
  | .pathOne h0 => ⟨(ren_ty hS h0).1, fun {Ψ' Φ' Δ ρ δ} hR =>
    by simp only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil]; exact EqTm0.pathOne (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil] using (ren_ty hS h0).2 hR)⟩
  | .splitL h0 h1 => ⟨(ren_ty hS h1).1, fun {Ψ' Φ' Δ ρ δ} hR =>
    by simp only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil]; exact EqTm0.splitL (ent_trans hR.ent (ent_subst h0 _)) (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil] using (ren_ty hS h1).2 hR)⟩
  | .splitR h0 h1 => ⟨(ren_ty hS h1).1, fun {Ψ' Φ' Δ ρ δ} hR =>
    by simp only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil]; exact EqTm0.splitR (ent_trans hR.ent (ent_subst h0 _)) (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil] using (ren_ty hS h1).2 hR)⟩
  | .transpFace h0 h1 => ⟨(ren_ty hS h1).1, fun {Ψ' Φ' Δ ρ δ} hR =>
    by simp only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil]; exact EqTm0.transpFace (ent_trans hR.ent (ent_subst h0 _)) (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil] using (ren_ty hS h1).2 hR)⟩
  | .hcompFace h0 h1 => ⟨(ren_ty hS h1).1, fun {Ψ' Φ' Δ ρ δ} hR =>
    by simp only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil]; exact EqTm0.hcompFace (ent_trans hR.ent (ent_subst h0 _)) (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil] using (ren_ty hS h1).2 hR)⟩
  | .transpU h0 => ⟨(ren_ty hS h0).1, fun {Ψ' Φ' Δ ρ δ} hR =>
    by simp only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil]; exact EqTm0.transpU (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil] using (ren_ty hS h0).2 hR)⟩
  | .transpPi h0 => ⟨(ren_ty hS h0).1, fun {Ψ' Φ' Δ ρ δ} hR =>
    by rw [transpPi_subst]; simp only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil]; exact EqTm0.transpPi (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil] using (ren_ty hS h0).2 hR)⟩
  | .transpSigma h0 => ⟨(ren_ty hS h0).1, fun {Ψ' Φ' Δ ρ δ} hR =>
    by rw [transpSigma_subst]; simp only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil]; exact EqTm0.transpSigma (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil] using (ren_ty hS h0).2 hR)⟩
  | .transpPath h0 => ⟨(ren_ty hS h0).1, fun {Ψ' Φ' Δ ρ δ} hR =>
    by rw [transpPath_subst]; simp only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil]; exact EqTm0.transpPath (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil] using (ren_ty hS h0).2 hR)⟩
  | .transpGlue h0 h1 h2 h3 h4 h5 => ⟨(ren_ty hS h0).1, fun {Ψ' Φ' Δ ρ δ} hR =>
    by
      have hφ := scoped_cof_right (scoped_of_ty h2)
      rw [transpGlueWith_subst]; simp only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil]
      exact EqTm0.transpGlue (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil] using (ren_ty hS h0).2 hR) ((ren_ty hS h1).2 hR.dup) (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil] using (ren_ty hS h2).2 (hR.dup.underCof hφ)) (hR.sc h3)
        (ent_trans (ent_subst h4 _) (by simpa only [Iup_rI] using (forall0_subst _ (rI δ)).1))
        (ent_trans (by simpa only [Iup_rI] using (forall0_subst _ (rI δ)).2) (ent_subst h5 _))⟩
  | .transpIPi h0 => ⟨(ren_ty hS h0).1, fun {Ψ' Φ' Δ ρ δ} hR =>
    by rw [transpIPi_subst]; simp only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil]; exact EqTm0.transpIPi (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil] using (ren_ty hS h0).2 hR)⟩
  | .hcompIPi h0 => ⟨(ren_ty hS h0).1, fun {Ψ' Φ' Δ ρ δ} hR =>
    by rw [hcompIPi_subst]; simp only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil]; exact EqTm0.hcompIPi (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil] using (ren_ty hS h0).2 hR)⟩
  | .hcompPi h0 => ⟨(ren_ty hS h0).1, fun {Ψ' Φ' Δ ρ δ} hR =>
    by rw [hcompPi_subst]; simp only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil]; exact EqTm0.hcompPi (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil] using (ren_ty hS h0).2 hR)⟩
  | .hcompSigma h0 => ⟨(ren_ty hS h0).1, fun {Ψ' Φ' Δ ρ δ} hR =>
    by rw [hcompSigma_subst]; simp only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil]; exact EqTm0.hcompSigma (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil] using (ren_ty hS h0).2 hR)⟩
  | .hcompPath h0 => ⟨(ren_ty hS h0).1, fun {Ψ' Φ' Δ ρ δ} hR =>
    by rw [hcompPath_subst]; simp only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil]; exact EqTm0.hcompPath (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil] using (ren_ty hS h0).2 hR)⟩
  | .hcompGlue h0 h1 h2 => ⟨(ren_ty hS h0).1, fun {Ψ' Φ' Δ ρ δ} hR =>
    by have hφ := scoped_cof_right (scoped_of_ty h2); rw [hcompGlue_subst]; simp only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil]; exact EqTm0.hcompGlue (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil] using (ren_ty hS h0).2 hR) ((ren_ty hS h1).2 hR) (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil] using (ren_ty hS h2).2 (hR.underCof hφ))⟩
  | .hcompU h0 => ⟨(ren_ty hS h0).1, fun {Ψ' Φ' Δ ρ δ} hR =>
    by rw [hcompU_subst]; simp only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil]; exact EqTm0.hcompU (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil] using (ren_ty hS h0).2 hR)⟩
  | .glueFace h0 h1 => ⟨(ren_ty hS h1).1, fun {Ψ' Φ' Δ ρ δ} hR =>
    by simp only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil]; exact EqTm0.glueFace (ent_trans hR.ent (ent_subst h0 _)) (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil] using (ren_ty hS h1).2 hR)⟩
  | .glueElFace h0 h1 => ⟨(ren_ty hS h1).1, fun {Ψ' Φ' Δ ρ δ} hR =>
    by simp only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil]; exact EqTm0.glueElFace (ent_trans hR.ent (ent_subst h0 _)) (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil] using (ren_ty hS h1).2 hR)⟩
  | .unglueFace h0 h1 h2 h3 => ⟨(ren_ty hS h1).1, fun {Ψ' Φ' Δ ρ δ} hR =>
    by simp only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil]; exact EqTm0.unglueFace (ent_trans hR.ent (ent_subst h0 _)) (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil] using (ren_ty hS h1).2 hR) ((ren_ty hS h2).2 hR) (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil] using (ren_ty hS h3).2 hR)⟩
  | .glueBeta h0 h1 => ⟨(ren_ty hS h0).1, fun {Ψ' Φ' Δ ρ δ} hR =>
    by simp only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil]; exact EqTm0.glueBeta (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil] using (ren_ty hS h0).2 hR) (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil] using (ren_ty hS h1).2 hR)⟩
  | .glueEta h0 => ⟨(ren_ty hS h0).1, fun {Ψ' Φ' Δ ρ δ} hR =>
    by simp only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil]; exact EqTm0.glueEta (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil] using (ren_ty hS h0).2 hR)⟩
  | .data h0 h1 h2 h3 => ⟨(ren_ty hS h1).1, fun {Ψ' Φ' Δ ρ δ} hR =>
    by simp only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil]; exact EqTm0.data h0 ((ren_ty hS h1).2 hR) ((ren_ty hS h2).2 hR) ((ren_eqtele hS h3).2 (fun k A hk => by simpa using hS.params _ _ _ _ h0 hk) hR)⟩
  | .con h0 h1 h2 h3 h4 h5 h6 h7 => ⟨(ren_ty hS h2).1, fun {Ψ' Φ' Δ ρ δ} hR =>
    by
      obtain ⟨D', C', hD', hC', hps, hlen, _, _⟩ := gen_con h2 rfl
      rw [h0] at hD'; cases hD'; rw [h1] at hC'; cases hC'
      have ht := (ren_eqtele hS h5).2 (fun k A hk => by
        rw [List.length_reverse, hlen]; exact argTys_closed hS h0 h1 k A hk) hR
      simp only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil]
      refine EqTm0.con h0 h1 (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil] using (ren_ty hS h2).2 hR) (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil] using (ren_ty hS h3).2 hR) ((ren_eqtele hS h4).2 (fun k A hk => by simpa using hS.params _ _ _ _ h0 hk) hR) ?_ (by simpa using h6) ?_
      · rw [toList_subst hps, ← List.map_reverse]; exact ht
      · intro k r r' hr hr'
        rw [List.getElem?_map] at hr hr'
        obtain ⟨r0, hr0, rfl⟩ := Option.map_eq_some_iff.1 hr
        obtain ⟨r0', hr0', rfl⟩ := Option.map_eq_some_iff.1 hr'
        exact I_eq_subst (h7 k r0 r0' hr0 hr0') _⟩
  | .elim h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 => ⟨(ren_ty hS h1).1, fun {Ψ' Φ' Δ ρ δ} hR =>
    by
      obtain ⟨D', hD', hps, hlen, _⟩ := gen_elim h1 rfl
      rw [h0] at hD'; cases hD'
      simp only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil]
      refine EqTm0.elim h0 (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil] using (ren_ty hS h1).2 hR) (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil] using (ren_ty hS h2).2 hR) ((ren_eqtele hS h3).2 (fun k A hk => by simpa using hS.params _ _ _ _ h0 hk) hR)
        ((ren_eq hS h4).2 (hR.up (ren_eq hS h4).1)) (isList_subst h5 _ _) (isList_subst h6 _ _)
        (by rw [toList_subst h5, toList_subst h6, List.length_map, List.length_map, h7]) ?_ ((ren_eq hS h9).2 hR)
      intro c C b b' hc hb hb'
      rw [toList_subst h5, List.getElem?_map] at hb
      rw [toList_subst h6, List.getElem?_map] at hb'
      obtain ⟨b0, hb0, rfl⟩ := Option.map_eq_some_iff.1 hb
      obtain ⟨b0', hb0', rfl⟩ := Option.map_eq_some_iff.1 hb'
      have := (ren_eq hS (h8 c C b0 b0' hc hb0 hb0')).2 hR
      rwa [branchTy_subst _ _ hS h0 hc hps hlen, up_rS] at this⟩
  | .conBnd h0 h1 h2 h3 h4 h5 h6 => ⟨(ren_ty hS h6).1, fun {Ψ' Φ' Δ ρ δ} hR =>
    by
      obtain ⟨D', C', hD', hC', _, hlen, hlena, hlenr⟩ := gen_con h6 rfl
      rw [h0] at hD'; cases hD'; rw [h1] at hC'; cases hC'
      have hb := hS.bnd _ _ _ _ _ _ _ h0 h1 h2
      rw [bndAt_subst _ _ (by rw [hlen, hlena, hlenr]; exact hb.2), ← toList_subst h4, ← toList_subst h5]
      exact EqTm0.conBnd h0 h1 h2 (by
          have := ent_trans hR.ent (ent_subst h3 (rI δ)); rwa [cofAt_subst _ (by rw [hlenr]; exact hb.1)] at this)
        (isList_subst h4 _ _) (isList_subst h5 _ _) ((ren_ty hS h6).2 hR)⟩
  | .elimCon h0 h1 h2 h3 h4 h5 h6 h7 => ⟨(ren_tele hS h6).1, fun {Ψ' Φ' Δ ρ δ} hR =>
    by
      obtain ⟨D', hD', _, hlen, _⟩ := gen_elim h7 rfl
      rw [h0] at hD'; cases hD'
      have ht := (ren_tele hS h6).2 (fun k A hk => by rw [List.length_reverse, hlen]; exact argTys_closed hS h0 h1 k A hk) hR
      rw [elimCon_subst h4]; simp only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil]
      refine EqTm0.elimCon h0 h1 ?_ (isList_subst h3 _ _) (isList_subst h4 _ _) (isList_subst h5 _ _) ?_ (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil] using (ren_ty hS h7).2 hR)
      · rw [toList_subst h5, List.getElem?_map, h2]; rfl
      · rw [toList_subst h3, ← List.map_reverse]; exact ht⟩
  | .elimHcomp h0 h1 h2 => ⟨(ren_ty hS h1).1, fun {Ψ' Φ' Δ ρ δ} hR =>
    by rw [elimHcomp_subst]; simp only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil]; exact EqTm0.elimHcomp h0 (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil] using (ren_ty hS h1).2 hR) (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil] using (ren_ty hS h2).2 hR)⟩
  | .transpData0 h0 h1 h2 => ⟨(ren_ty hS h2).1, fun {Ψ' Φ' Δ ρ δ} hR =>
    by simp only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil]; exact EqTm0.transpData0 h0 h1 (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil] using (ren_ty hS h2).2 hR)⟩
  | .transpCon h0 h1 h2 h3 h4 h5 h6 => ⟨(ren_tele hS h5).1, fun {Ψ' Φ' Δ ρ δ} hR =>
    by
      obtain ⟨D', hD', hlen0⟩ := gen_transp_data h6 rfl
      rw [h0] at hD'; cases hD'
      have hlen := hlen0
      rw [← List.length_map (f := (·.dinst .zero)), ← dinst_toList h3] at hlen
      have ht := (ren_tele hS h5).2 (fun k A hk => by rw [List.length_reverse, hlen]; exact argTys_closed hS h0 h2 k A hk) hR
      rw [transpCon_subst hS h0 h2 h3 h4 hlen0]; simp only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil]
      refine EqTm0.transpCon h0 h1 h2 (isList_subst h3 _ _) (isList_subst h4 _ _) ?_ (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil] using (ren_ty hS h6).2 hR)
      rw [dinst_toList (isList_subst h3 _ _), toList_subst h3]
      rw [dinst_toList h3] at ht
      simpa only [List.map_reverse, List.map_map, Function.comp_def, dinst_subst, I.subst, Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil] using ht⟩
  | .transpHcomp h0 h1 h2 h3 => ⟨(ren_ty hS h2).1, fun {Ψ' Φ' Δ ρ δ} hR =>
    by rw [transpHcomp_subst]; simp only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil]; exact EqTm0.transpHcomp h0 h1 (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil] using (ren_ty hS h2).2 hR) (by simpa only [Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil] using (ren_ty hS h3).2 hR)⟩
end

end KubusCore.Meta
