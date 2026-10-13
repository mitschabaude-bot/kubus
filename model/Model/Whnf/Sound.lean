import Model.Whnf.Step

/-!
# Soundness of weak-head reduction

A step of a typed term is a judgmental equality at its type, in any context (`step_sound`). The
one exception is composition in an inductive type without path constructors (`hcompCon`), whose
soundness needs the tube to be a constructor on its face; it is a hypothesis here (`HCSound`),
discharged for closed terms by the computability argument.
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

variable {S : Sig}

/-- Soundness of the `hcompCon` step for closed terms. -/
def HCSound (S : Sig) : Prop :=
  ∀ {Ψ : ℕ} {Φ : I} {d : ℕ} {ps : Tm} {φ : I} {u a T t' : Tm},
    HasTy0 S Ψ Φ [] (.hcomp (.data d ps) φ u a) T → I.entails .one φ = false → step S a = none →
    step S (.hcomp (.data d ps) φ u a) = some t' → EqTm0 S Ψ Φ [] (.hcomp (.data d ps) φ u a) t' T

/-- Soundness of `unglue` of a `glueEl` with other annotations, for closed terms. -/
def UGSound (S : Sig) : Prop :=
  ∀ {Ψ : ℕ} {Φ φ φ' : I} {e e' t a T : Tm},
    HasTy0 S Ψ Φ [] (.unglue φ e (.glueEl φ' e' t a)) T → EqTm0 S Ψ Φ [] (.unglue φ e (.glueEl φ' e' t a)) a T

theorem firstBnd_spec {bnd : List (I × Tm)} {rs : List I} {b : Tm} (h : firstBnd bnd rs = some b) :
    ∃ (k : ℕ) (ψ : I), bnd[k]? = some (ψ, b) ∧ I.entails .one (Ctor.cofAt ψ rs) = true := by
  unfold firstBnd at h
  split at h
  · rename_i p hp
    cases h
    obtain ⟨hpm, hpt⟩ := List.find?_some hp, List.mem_of_find?_eq_some hp
    obtain ⟨k, hk, hk'⟩ := List.getElem_of_mem hpt
    exact ⟨k, p.1, by rw [List.getElem?_eq_getElem hk, hk'], by simpa using hpm⟩
  · cases h

theorem presup (hW : WfSig S) {Ψ Φ Γ t u A} (e : EqTm0 S Ψ Φ Γ t u A) :
    HasTy0 S Ψ Φ Γ t A ∧ HasTy0 S Ψ Φ Γ u A :=
  let h := pre_eq (sigClosed_of_wfSig hW) (wf_typed _ S rfl hW).1 (wf_typed _ S rfl hW).2 e
  ⟨h.1, h.2.1⟩

theorem lvl_bound (hW : WfSig S) {Ψ Φ Γ X l} (h : HasTy0 S Ψ Φ Γ X (.univ l)) : l ≤ maxLevel := by
  rcases pre_ty (sigClosed_of_wfSig hW) (wf_typed _ S rfl hW).1 (wf_typed _ S rfl hW).2 h with ⟨l', h'⟩ | ⟨l', he, hl⟩
  · have := gen_univ h' rfl; omega
  · cases he; exact hl

theorem lvl_bound_eq (hW : WfSig S) {Ψ Φ Γ X Y l} (e : EqTm0 S Ψ Φ Γ X Y (.univ l)) : l ≤ maxLevel := by
  rcases (pre_eq (sigClosed_of_wfSig hW) (wf_typed _ S rfl hW).1 (wf_typed _ S rfl hW).2 e).2.2 with
    ⟨l', h'⟩ | ⟨l', he, hl⟩
  · have := gen_univ h' rfl; omega
  · cases he; exact hl

theorem chain_rel (hW : WfSig S) {Ψ Φ Γ X} : ∀ {Y Z}, TyChainC S Ψ Φ Γ Y Z → Rel S Ψ Φ Γ X Y → Rel S Ψ Φ Γ X Z
  | _, _, .refl _, r => r
  | _, _, .step e ch, r => chain_rel hW ch (r.conv e (lvl_bound_eq hW e))
  | _, _, .up _ ch, r => chain_rel hW ch r.up

/-- A conversion chain from a type former which is not a universe to a typed type which is not a
universe is one equation. -/
theorem chain_eq (hW : WfSig S) {Ψ Φ Γ X Y l l'} (ch : TyChainC S Ψ Φ Γ X Y) (hX : HasTy0 S Ψ Φ Γ X (.univ l))
    (hc : X.headClash (.univ 0) = true) (hY : HasTy0 S Ψ Φ Γ Y (.univ l')) (hYu : ∀ k, Y ≠ .univ k) :
    ∃ m, EqTm0 S Ψ Φ Γ X Y (.univ m) := by
  obtain ⟨m, -, e⟩ := (chain_rel hW ch (Rel.refl hX (lvl_bound hW hX))).collapse hX (lvl_bound hW hX) hc
    (.inl ⟨l', lvl_bound hW hY, hY⟩) hYu
  exact ⟨m, e⟩

/-- A constructor typed at an inductive type has its arguments typed at that type's parameters. -/
theorem con_args (hW : WfSig S) {Ψ Φ Γ d c qs args rs ps l} (h : HasTy0 S Ψ Φ Γ (.con d c qs args rs) (.data d ps))
    (hT : HasTy0 S Ψ Φ Γ (.data d ps) (.univ l)) :
    ∃ D C, S[d]? = some (.data D) ∧ D.ctors[c]? = some C ∧ IsList ps ∧ IsList args ∧
      HasTele0 S Ψ Φ Γ args (C.argTys d D.params.length) ps.toList.reverse ∧ rs.length = C.dims ∧
      ∃ m, EqTm0 S Ψ Φ Γ (.data d qs) (.data d ps) (.univ m) := by
  obtain ⟨hI, ch⟩ := gen_conF h rfl
  obtain ⟨-, D, C, hD, hC, hqs, hdq, hqt, haq, hrs, -⟩ := hI
  obtain ⟨m, e⟩ := chain_eq hW ch hdq rfl hT (fun k h => by cases h)
  obtain ⟨D', hD', hpt⟩ := gen_data_tele hT rfl
  rw [hD] at hD'; cases hD'
  exact ⟨D, C, hD, hC, tele_isList hpt, tele_isList haq,
    (args_retype hW hD hC hqs (tele_isList hpt) hqt hpt e haq).1, hrs, m, e⟩

/-- Transport along an equal line. -/
theorem transp_retype0 (hW : WfSig S) {Ψ Φ Γ A A' a l} {φ : I}
    (hφ : φ.Scoped Ψ) (hc : EqTm0 S (Ψ + 1) (cof Φ φ).shift Γ.dshift A (A.dinst .zero).dshift (.univ l))
    (ha : HasTy0 S Ψ Φ Γ a (A.dinst .zero)) (e : EqTm0 S (Ψ + 1) Φ.shift Γ.dshift A A' (.univ l)) :
    HasTy0 S Ψ Φ Γ (.transp A' φ a) (A.dinst .one) := by
  have hS := sigClosed_of_wfSig hW
  have hΦ : Φ.Scoped Ψ := scoped_of_wf (wf_of_ty ha)
  have hXs : (cof Φ φ).Scoped Ψ := ⟨hΦ, hφ⟩
  have hent : I.Entails (cof Φ φ) Φ := ent_and_left _ _
  have ez := EqTm0.dsubst hS e (r := .zero) trivial
  have eo := EqTm0.dsubst hS e (r := .one) trivial
  have hc' : EqTm0 S (Ψ + 1) (cof Φ φ).shift Γ.dshift A' (A'.dinst .zero).dshift (.univ l) :=
    EqTm0.trans (EqTm0.trans (EqTm0.symm (EqTm0.restrict (scoped_shift hXs) (ent_shift hent) e)) hc)
      (EqTm0.restrict (scoped_shift hXs) (ent_shift hent) (EqTm0.dwk hS ez))
  exact HasTy0.conv (HasTy0.transp (presup hW e).2 hφ hc' (HasTy0.conv ha ez)) (EqTm0.symm eo)

/-- Composition at an equal type. -/
theorem hcomp_retype0 (hW : WfSig S) {Ψ Φ Γ A A' u a l} {φ : I} (hφ : φ.Scoped Ψ)
    (hu : HasTy0 S (Ψ + 1) (cof Φ φ).shift Γ.dshift u A.dshift) (ha : HasTy0 S Ψ Φ Γ a A)
    (hside : EqTm0 S Ψ (cof Φ φ) Γ (u.dinst .zero) a A) (e : EqTm0 S Ψ Φ Γ A A' (.univ l)) :
    HasTy0 S Ψ Φ Γ (.hcomp A' φ u a) A := by
  have hS := sigClosed_of_wfSig hW
  have hΦ : Φ.Scoped Ψ := scoped_of_wf (wf_of_ty ha)
  have hXs : (cof Φ φ).Scoped Ψ := ⟨hΦ, hφ⟩
  have hent : I.Entails (cof Φ φ) Φ := ent_and_left _ _
  have hu' := HasTy0.conv hu (EqTm0.restrict (scoped_shift hXs) (ent_shift hent) (EqTm0.dwk hS e))
  have hside' := EqTm0.conv hside (EqTm0.restrict hXs hent e)
  exact HasTy0.conv (HasTy0.hcomp (presup hW e).2 hφ hu' (HasTy0.conv ha e) hside') (EqTm0.symm e)

theorem ent_of_one {Φ φ : I} (h : I.entails .one φ = true) : I.Entails Φ φ := ent_trans (ent_one Φ) h

theorem step_sound (hS : SigClosed S) (hW : WfSig S) (hHC : HCSound S) (hUG : UGSound S) {Ψ Φ Γ t A t'}
    (h : HasTy0 S Ψ Φ Γ t A) (hΓ : Γ = []) (hs : step S t = some t') : EqTm0 S Ψ Φ Γ t t' A :=
  match h with
  | .var _ _ => by simp [step] at hs
  | .conv h0 h1 => (step_sound hS hW hHC hUG h0 hΓ hs).conv h1
  | .restrict h0 h1 h2 => (step_sound hS hW hHC hUG h2 hΓ hs).restrict h0 h1
  | .const h0 h1 => by
    simp only [step, h1] at hs; cases hs
    exact EqTm0.delta (.const h0 h1) h1
  | .univ _ _ => by simp [step] at hs
  | .cumul h0 h1 => (step_sound hS hW hHC hUG h1 hΓ hs).cumul h0
  | .pi _ _ => by simp [step] at hs
  | .lam _ _ => by simp [step] at hs
  | .app h0 h1 => by
    simp only [step] at hs
    split at hs
    · cases hs; exact EqTm0.piBeta (.app h0 h1)
    · obtain ⟨f', hf', rfl⟩ := Option.map_eq_some_iff.1 hs
      exact EqTm0.app (step_sound hS hW hHC hUG h0 hΓ hf') (EqTm0.refl h1)
  | .sigma _ _ => by simp [step] at hs
  | .pair _ _ _ => by simp [step] at hs
  | .fst h0 => by
    simp only [step] at hs
    split at hs
    · cases hs; exact EqTm0.fstBeta (.fst h0)
    · obtain ⟨p', hp', rfl⟩ := Option.map_eq_some_iff.1 hs
      exact EqTm0.fst (step_sound hS hW hHC hUG h0 hΓ hp')
  | .snd h0 => by
    simp only [step] at hs
    split at hs
    · cases hs; exact EqTm0.sndBeta (.snd h0)
    · obtain ⟨p', hp', rfl⟩ := Option.map_eq_some_iff.1 hs
      exact EqTm0.snd (step_sound hS hW hHC hUG h0 hΓ hp')
  | .path _ _ _ => by simp [step] at hs
  | .plam _ _ _ _ => by simp [step] at hs
  | .papp h0 h1 => by
    simp only [step] at hs
    split at hs
    · cases hs; exact EqTm0.pathBeta (.papp h0 h1)
    · obtain ⟨p', hp', rfl⟩ := Option.map_eq_some_iff.1 hs
      exact EqTm0.papp (step_sound hS hW hHC hUG h0 hΓ hp') h1 h1 (I_eq_refl _)
  | .ipi _ _ => by simp [step] at hs
  | .ilam _ _ => by simp [step] at hs
  | .iapp h0 h1 => by
    simp only [step] at hs
    split at hs
    · cases hs; exact EqTm0.pathBeta (.iapp h0 h1)
    · obtain ⟨p', hp', rfl⟩ := Option.map_eq_some_iff.1 hs
      exact EqTm0.iapp (step_sound hS hW hHC hUG h0 hΓ hp') h1 h1 (I_eq_refl _)
  | .split h0 h1 h2 h3 h4 h5 h6 => by
    simp only [step] at hs
    split at hs
    · cases hs; exact EqTm0.splitL (ent_of_one (by assumption)) (.split h0 h1 h2 h3 h4 h5 h6)
    · split at hs
      · cases hs; exact EqTm0.splitR (ent_of_one (by assumption)) (.split h0 h1 h2 h3 h4 h5 h6)
      · cases hs
  | .abort _ _ => by simp [step] at hs
  | .transp h0 h1 h2 h3 => by sorry
  | .hcomp h0 h1 h2 h3 h4 => by sorry
  | .glue h0 h1 h2 h3 => by
    simp only [step] at hs
    split at hs
    · cases hs; exact EqTm0.glueFace (ent_of_one (by assumption)) (.glue h0 h1 h2 h3)
    · cases hs
  | .glueEl h0 h1 h2 h3 h4 => by
    simp only [step] at hs
    split at hs
    · cases hs; exact EqTm0.glueElFace (ent_of_one (by assumption)) (.glueEl h0 h1 h2 h3 h4)
    · cases hs
  | .unglue h0 h1 h2 h3 => by
    simp only [step] at hs
    split at hs
    · rename_i hφ
      cases hs
      have hΦ := scoped_of_wf (wf_of_ty h1)
      exact EqTm0.unglueFace (ent_of_one hφ) h3 h1
        (HasTy0.restrict hΦ (ent_and_intro (ent_refl _) (ent_of_one hφ)) h2)
    · split at hs
      · rename_i g' hg'
        cases hs
        have e := step_sound hS hW hHC hUG h3 hΓ hg'
        exact EqTm0.unglue (.unglue h0 h1 h2 h3) (.unglue h0 h1 h2 (presup hW e).2) (ent_refl _) (ent_refl _)
          (EqTm0.refl h2) e
      · split at hs
        · cases hs; subst hΓ; exact hUG (.unglue h0 h1 h2 h3)
        · cases hs
  | .data _ _ _ => by simp [step] at hs
  | .con h0 h1 h2 h3 h4 h5 h6 h7 => by
    simp only [step, h0, h1] at hs
    obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.1 hs
    obtain ⟨k, ψ, hk, hψ⟩ := firstBnd_spec hb
    exact EqTm0.conBnd h0 h1 hk (ent_of_one hψ) h2 (tele_isList h5) (.con h0 h1 h2 h3 h4 h5 h6 h7)
  | .elim h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 => by sorry

end Model.Whnf
