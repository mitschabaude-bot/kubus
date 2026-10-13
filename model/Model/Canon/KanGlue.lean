import Model.Canon.KanUniv

/-!
# Canonicity: the Kan operations in Glue types

Composition (`hcompGlue`) and transport (`transpGlue`) in a Glue type whose base, fibre and
equivalence are computable (and whose base and fibre are Kan) are computable.
-/

set_option autoImplicit false

namespace Model.Canon

open KubusCore KubusCore.Meta

noncomputable section

variable {S : Sig} {k k' m : ℕ}

theorem TubeC.isub {A u : Tm} {φ : I} (hu : TubeC S k A φ u) (σ : ISub k' k) :
    TubeC S k' (A.isub σ) (φ.subst σ.τ) (u.isub σ.up) := by
  intro k'' σ' r hr hh
  have e1 : φ.subst (σ.comp σ').τ = (φ.subst σ.τ).subst σ'.τ := (I_subst_subst _ _ _).symm
  have := hu k'' (σ.comp σ') r hr (by rw [e1]; exact hh)
  rw [Tm.isub_isub, Tm.isub_isub, ← ISub.up_comp]; exact this

/-- Computability data of a closed Glue type (its base, and its fibre and equivalence where the face holds). -/
structure GlueL (S : Sig) (n : ℕ) (A : Tm) (φ : I) (T e : Tm) : Prop where
  ty : ∃ l, HasTy S n .one [] (.glue A φ T e) (.univ l)
  rtA : ∀ k' (σ : ISub k' n), RT S k' (A.isub σ)
  kA : KanAll S n A
  rtT : ∀ k' (σ : ISub k' n), (ival (idEnv k') (φ.subst σ.τ)).holds → RT S k' (T.isub σ)
  kTH : ∀ k' (σ : ISub k' n), (ival (idEnv k') (φ.subst σ.τ)).holds → KanH S k' (T.isub σ)
  kTT : ∀ k' (σ : ISub (k' + 1) n), (ival (idEnv (k' + 1)) (φ.subst σ.τ)).holds → KanT S k' (T.isub σ)
  eqv : ∀ k' (σ : ISub k' n), (ival (idEnv k') (φ.subst σ.τ)).holds →
    RE S k' (Tm.equiv (T.isub σ) (A.isub σ)) (e.isub σ)

section
open Tm
/-- The typings of the parts of `hcompGlue` (adapted from `KubusCore.Meta.hcompGlue_typed`). -/
theorem hcompGlue_parts (hS : SigClosed S) {Ψ Φ Γ A φ T e ψ u u0 l}
    (h : HasTy0 S Ψ Φ Γ (hcomp (glue A φ T e) ψ u u0) (glue A φ T e)) (hG : HasTy0 S Ψ Φ Γ (glue A φ T e) (univ l)) :
    HasTy0 S Ψ (cof Φ φ) Γ (hcomp T ψ u u0) T ∧
    HasTy0 S Ψ Φ Γ (hcomp A (.or ψ φ) (Meta.glueTube φ T e ψ u u0) (unglue φ e u0)) A ∧
    HasTy0 S (Ψ + 1) (cof Φ (.or ψ φ)).shift Γ.dshift (Meta.glueTube φ T e ψ u u0) A.dshift ∧
    HasTy0 S (Ψ + 1) (cof (cof Φ φ) ψ).shift Γ.dshift u T.dshift ∧
    HasTy0 S Ψ (cof Φ φ) Γ u0 T := by
  obtain ⟨l1, ⟨-, hψ, hu, hu0, hside⟩, -⟩ := gen_hcomp h rfl
  obtain ⟨l0, ⟨hA0, hφ, hT0, he⟩, chg⟩ := gen_glue hS hG rfl
  have hA := chg.transport hA0
  have hs := scoped_of_ty h
  have hXφ : (cof Φ φ).Scoped Ψ := ⟨hs, hφ⟩
  have hXψ : (cof Φ ψ).Scoped Ψ := ⟨hs, hψ⟩
  have hT := (chg.restrict hXφ (ent_and_left _ _)).transport hT0
  -- under `φ` the Glue type is `T`
  have hGφ := HasTy0.restrict hXφ (ent_and_left _ _) hG
  have eGT : EqTm0 S Ψ (cof Φ φ) Γ (glue A φ T e) T (univ l) := EqTm0.glueFace (ent_and_right _ _) hGφ
  have hXφψ : (cof (cof Φ φ) ψ).Scoped Ψ := ⟨hXφ, hψ⟩
  have eGTψ := EqTm0.restrict hXφψ (ent_and_left _ _) eGT
  have huT : HasTy0 S (Ψ + 1) (cof (cof Φ φ) ψ).shift Γ.dshift u T.dshift :=
    HasTy0.conv (HasTy0.restrict (scoped_shift hXφψ)
      (ent_shift (ent_and_mono (ent_and_left _ _) (ent_refl _))) hu) (EqTm0.dwk hS eGTψ)
  have hu0T : HasTy0 S Ψ (cof Φ φ) Γ u0 T := HasTy0.conv (HasTy0.restrict hXφ (ent_and_left _ _) hu0) eGT
  have hsideT : EqTm0 S Ψ (cof (cof Φ φ) ψ) Γ (u.dinst .zero) u0 T :=
    EqTm0.conv (EqTm0.restrict hXφψ (ent_and_mono (ent_and_left _ _) (ent_refl _)) hside) eGTψ
  have htc := HasTy0.hcomp hT hψ huT hu0T hsideT
  obtain ⟨hfl, hfl0, hfl1, hflψ⟩ := hfill_typed hS hT hψ huT hu0T hsideT
  -- the tube of the base
  have hYs : (cof Φ (.or ψ φ)).Scoped Ψ := ⟨hs, ⟨hψ, hφ⟩⟩
  have hRs : (cof Φ (.or ψ φ)).shift.Scoped (Ψ + 1) := scoped_shift hYs
  have hRΦ : I.Entails (cof Φ (.or ψ φ)).shift Φ.shift := ent_shift (ent_and_left _ _)
  have hA1 := HasTy0.restrict hRs hRΦ (HasTy0.dwk hS hA)
  have hψ1 : ψ.shift.Scoped (Ψ + 1) := scoped_shift hψ
  have hφ1 : φ.shift.Scoped (Ψ + 1) := scoped_shift hφ
  have hX1 : (cof (cof Φ (.or ψ φ)).shift ψ.shift).Scoped (Ψ + 1) := ⟨hRs, hψ1⟩
  have hX2 : (cof (cof Φ (.or ψ φ)).shift φ.shift).Scoped (Ψ + 1) := ⟨hRs, hφ1⟩
  have hX3 : (cof (cof (cof Φ (.or ψ φ)).shift ψ.shift) φ.shift).Scoped (Ψ + 1) := ⟨hX1, hφ1⟩
  have hX1ψ : I.Entails (cof (cof Φ (.or ψ φ)).shift ψ.shift) (cof Φ ψ).shift :=
    ent_and_intro (ent_trans (ent_and_left _ _) hRΦ) (ent_and_right _ _)
  have hX2φ : I.Entails (cof (cof Φ (.or ψ φ)).shift φ.shift) (cof Φ φ).shift :=
    ent_and_intro (ent_trans (ent_and_left _ _) hRΦ) (ent_and_right _ _)
  have hX3φ : I.Entails (cof (cof (cof Φ (.or ψ φ)).shift ψ.shift) φ.shift) (cof Φ φ).shift :=
    ent_and_intro (ent_trans (ent_and_left _ _) (ent_trans (ent_and_left _ _) hRΦ)) (ent_and_right _ _)
  have hX3φψ : I.Entails (cof (cof (cof Φ (.or ψ φ)).shift ψ.shift) φ.shift) (cof (cof Φ φ) ψ).shift :=
    ent_and_intro hX3φ (ent_trans (ent_and_left _ _) (ent_and_right _ _))
  have heD : HasTy0 S (Ψ + 1) (cof Φ φ).shift Γ.dshift e.dshift (equiv T.dshift A.dshift) := by
    have := HasTy0.dwk hS he
    rwa [equiv_dshift] at this
  have hGD : HasTy0 S (Ψ + 1) Φ.shift Γ.dshift (glue A.dshift φ.shift T.dshift e.dshift) (univ l) :=
    HasTy0.dwk hS hG
  have hb1 : HasTy0 S (Ψ + 1) (cof (cof Φ (.or ψ φ)).shift ψ.shift) Γ.dshift
      (unglue φ.shift e.dshift u) A.dshift :=
    HasTy0.unglue (HasTy0.restrict hX1 (ent_trans (ent_and_left _ _) hRΦ) hGD)
      (HasTy0.restrict hX1 (ent_and_left _ _) hA1)
      (HasTy0.restrict ⟨hX1, hφ1⟩ (ent_and_intro (ent_trans (ent_and_left _ _)
        (ent_trans (ent_and_left _ _) hRΦ)) (ent_and_right _ _)) heD)
      (HasTy0.restrict hX1 hX1ψ hu)
  have hb2 : HasTy0 S (Ψ + 1) (cof (cof Φ (.or ψ φ)).shift φ.shift) Γ.dshift
      (app (fst e.dshift) (hfill T ψ u u0)) A.dshift :=
    app_fst_equiv (HasTy0.restrict hX2 hX2φ heD) (HasTy0.restrict hX2 hX2φ hfl)
  have hover : EqTm0 S (Ψ + 1) (cof (cof (cof Φ (.or ψ φ)).shift ψ.shift) φ.shift) Γ.dshift
      (unglue φ.shift e.dshift u) (app (fst e.dshift) (hfill T ψ u u0)) A.dshift := by
    have he3 := HasTy0.restrict hX3 hX3φ heD
    have e1 := EqTm0.unglueFace (ent_and_right _ _)
      (HasTy0.restrict hX3 (ent_trans (ent_and_left _ _) hX1ψ) hu)
      (HasTy0.restrict hX3 (ent_trans (ent_and_left _ _) (ent_and_left _ _)) hA1) he3
    have e2 := app_fst_congr he3 (EqTm0.symm (EqTm0.restrict hX3 hX3φψ hflψ))
    exact EqTm0.trans e1 e2
  have htube : HasTy0 S (Ψ + 1) (cof Φ (.or ψ φ)).shift Γ.dshift (Meta.glueTube φ T e ψ u u0) A.dshift :=
    HasTy0.split hψ1 hφ1 (ent_shift (ent_and_right Φ (.or ψ φ))) hA1 hb1 hb2 hover
  have hu0g := HasTy0.unglue hG hA he hu0
  -- the side condition of the base
  have htube0 := HasTy0.dsubst hS (Φ := cof Φ (.or ψ φ)) htube (r := .zero) trivial
  rw [Meta.dshift_dinst, glueTube_d] at htube0
  have hud : HasTy0 S Ψ (cof Φ ψ) Γ (u.dinst .zero) (glue A φ T e) := by
    have := HasTy0.dsubst hS (Φ := cof Φ ψ) hu (r := .zero) trivial
    rwa [Meta.dshift_dinst] at this
  have hside' : EqTm0 S Ψ (cof Φ (.or ψ φ)) Γ ((Meta.glueTube φ T e ψ u u0).dinst .zero) (unglue φ e u0) A := by
    rw [glueTube_d]
    refine EqTm0.local (φ := ψ) (ψ := φ) hψ hφ (ent_and_right _ _) htube0
      (HasTy0.restrict hYs (ent_and_left _ _) hu0g) ?_ ?_
    · have hZ : (cof (cof Φ (.or ψ φ)) ψ).Scoped Ψ := ⟨hYs, hψ⟩
      have hZψ : I.Entails (cof (cof Φ (.or ψ φ)) ψ) (cof Φ ψ) :=
        ent_and_intro (ent_trans (ent_and_left _ _) (ent_and_left _ _)) (ent_and_right _ _)
      have hZΦ : I.Entails (cof (cof Φ (.or ψ φ)) ψ) Φ := ent_trans (ent_and_left _ _) (ent_and_left _ _)
      have e1 := EqTm0.splitL (ent_and_right _ _) (HasTy0.restrict hZ (ent_and_left _ _) htube0)
      have hZφ : (cof (cof (cof Φ (.or ψ φ)) ψ) φ).Scoped Ψ := ⟨hZ, hφ⟩
      have heZ := HasTy0.restrict hZφ (ent_and_mono hZΦ (ent_refl _)) he
      have hl := HasTy0.unglue (HasTy0.restrict hZ hZΦ hG) (HasTy0.restrict hZ hZΦ hA) heZ
        (HasTy0.restrict hZ hZψ hud)
      have hr := HasTy0.restrict hZ hZΦ hu0g
      have e2 := EqTm0.unglue hl hr (ent_refl _) (ent_refl _) (EqTm0.refl heZ)
        (EqTm0.restrict hZ hZψ hside)
      exact EqTm0.trans e1 e2
    · have hZ : (cof (cof Φ (.or ψ φ)) φ).Scoped Ψ := ⟨hYs, hφ⟩
      have hZφ : I.Entails (cof (cof Φ (.or ψ φ)) φ) (cof Φ φ) :=
        ent_and_intro (ent_trans (ent_and_left _ _) (ent_and_left _ _)) (ent_and_right _ _)
      have hZΦ : I.Entails (cof (cof Φ (.or ψ φ)) φ) Φ := ent_trans (ent_and_left _ _) (ent_and_left _ _)
      have e1 := EqTm0.splitR (ent_and_right _ _) (HasTy0.restrict hZ (ent_and_left _ _) htube0)
      have heZ := HasTy0.restrict hZ hZφ he
      have e2 := app_fst_congr heZ (EqTm0.restrict hZ hZφ hfl0)
      have e3 := EqTm0.unglueFace (ent_and_right _ _) (HasTy0.restrict hZ hZΦ hu0)
        (HasTy0.restrict hZ hZΦ hA) heZ
      exact EqTm0.trans e1 (EqTm0.trans e2 (EqTm0.symm e3))
  have hbase := HasTy0.hcomp hA (show (I.or ψ φ).Scoped Ψ from ⟨hψ, hφ⟩) htube hu0g hside'
  -- the side condition of the Glue element
  have hgside : EqTm0 S Ψ (cof Φ φ) Γ (app (fst e) (hcomp T ψ u u0))
      (hcomp A (.or ψ φ) (Meta.glueTube φ T e ψ u u0) (unglue φ e u0)) A := by
    have hYφ : I.Entails (cof Φ φ) (cof Φ (.or ψ φ)) :=
      ent_and_intro (ent_and_left _ _) (ent_trans (ent_and_right _ _) (ent_or_right _ _))
    have b1 := EqTm0.hcompFace (ent_trans (ent_and_right _ _) (ent_or_right _ _))
      (HasTy0.restrict hXφ (ent_and_left _ _) hbase)
    rw [glueTube_d] at b1
    have ht1 := HasTy0.dsubst hS (Φ := cof Φ (.or ψ φ)) htube (r := .one) trivial
    rw [Meta.dshift_dinst, glueTube_d] at ht1
    have b2 := EqTm0.splitR (ent_and_right _ _) (HasTy0.restrict hXφ hYφ ht1)
    have b3 := app_fst_congr he hfl1
    exact EqTm0.symm (EqTm0.trans b1 (EqTm0.trans b2 b3))
  exact ⟨htc, hbase, htube, huT, hu0T⟩

end

variable (hW : WfSig S) (hGC : GlueCompat S)
include hW

include hGC in
/-- `unglue` of a computable element of a Glue type with a computable equivalence. -/
theorem RE_unglue_gen {A T e g : Tm} {φ : I} {l : ℕ} (hG : HasTy S k .one [] (.glue A φ T e) (.univ l))
    (heqv : ∀ k' (σ : ISub k' k), (ival (idEnv k') (φ.subst σ.τ)).holds →
      RE S k' (Tm.equiv (T.isub σ) (A.isub σ)) (e.isub σ))
    (hg : RE S k (.glue A φ T e) g) : RE S k A (.unglue φ e g) := by
  obtain ⟨hφs, l', hAt, he⟩ := glue_data hW hG
  have hc := closed_of_ty hW hG
  simp only [Tm.closedB, Bool.and_eq_true] at hc
  have hgt := (Comp_el_typed hg).1
  have hu : HasTy S k .one [] (.unglue φ e g) A := unglue_ty hW ⟨l, .inl hG⟩ ⟨l', hAt, he⟩ hgt
  by_cases hφ : (ival (idEnv k) φ).holds
  · have hent := entails_of_holds hφs hφ
    have eGT := EqTm.glueFace hent hG
    have hgT := hg.conv_ty hW (.inr ⟨l, eGT⟩)
    have heq := heqv k (ISub.id k) (by rw [I_subst_id hφs]; exact hφ)
    rw [isub_id_of_closed hc.1.2, isub_id_of_closed hc.1.1.1, isub_id_of_closed hc.2] at heq
    unfold Tm.equiv at heq
    have hf := RE_pi_elim hW (RE_sigma_elim hW heq).1 hgT
    rw [shift_inst] at hf
    have he' : HasTy S k .one [] e (Tm.equiv T A) := (Comp_el_typed heq).1
    exact hf.conv hW (TyEq.refl _) (EqTm.unglueFace hent hgt hAt he').symm
  · have h := (RE_glue_elim hW hGC hG hφ hg).1 k (ISub.id k)
    rwa [← isub_unglue, isub_id_of_closed (closed_of_ty hW hu), isub_id_of_closed (closed_of_ty hW hAt)] at h

omit hW in
theorem glueTube_subst (φ : I) (T e : Tm) (ψ : I) (u u0 : Tm) (σ : ℕ → Tm) (τ : ℕ → I) :
    (Meta.glueTube φ T e ψ u u0).subst (dupS σ) (I.up τ) =
      Meta.glueTube (φ.subst τ) (T.subst σ τ) (e.subst σ τ) (ψ.subst τ) (u.subst (dupS σ) (I.up τ)) (u0.subst σ τ) := by
  simp only [Meta.glueTube, Tm.hfill]; scalc

omit hW in
theorem dupS_var : dupS Tm.var = Tm.var := funext fun _ => rfl

omit hW in
theorem glueTube_isub (φ : I) (T e : Tm) (ψ : I) (u u0 : Tm) (σ : ISub k' k) :
    (Meta.glueTube φ T e ψ u u0).isub σ.up =
      Meta.glueTube (φ.subst σ.τ) (T.isub σ) (e.isub σ) (ψ.subst σ.τ) (u.isub σ.up) (u0.isub σ) := by
  have := glueTube_subst φ T e ψ u u0 Tm.var σ.τ
  rw [dupS_var] at this
  exact this

/-- A closed term at stage `k + 1`, instantiated at `r`, as a restriction. -/
theorem isub_cons_id_dinst {x : Tm} {n : ℕ} (hx : x.closedB n (k + 1) = true) (r : I) (hr : r.Scoped k) :
    x.isub (ISub.cons r hr (ISub.id k)) = x.dinst r := by
  rw [← isub_up_dinst, isub_up_id_of_closed hx]

omit hW in
theorem holds_restr {φ : I} (hφ : φ.Scoped k) (σ : ISub k' k) {k'' : ℕ} (σ' : ISub k'' k')
    (hh : (ival (idEnv k') (φ.subst σ.τ)).holds) : (ival (idEnv k'') (φ.subst (σ.comp σ').τ)).holds :=
  holds_comp hφ σ hh (σ.comp σ') σ'.τ (fun _ _ => rfl)

include hGC in
/-- Composition in a computable Glue type. -/
theorem kanH_glue {A T e : Tm} {φ : I} (hD : GlueL S k A φ T e) : KanH S k (.glue A φ T e) := by
  intro ψ u u0 hty hu hu0
  by_cases hψ : (ival (idEnv k) ψ).holds
  · exact RE_hcomp_face hW hty hu hψ
  have hS := sigClosed_of_wfSig hW
  obtain ⟨lG, hG⟩ := hD.ty
  obtain ⟨hφs, l', hAt, he⟩ := glue_data hW hG
  by_cases hn : (ival (idEnv k) φ).holds
  · have hc := closed_of_ty hW hG
    simp only [Tm.closedB, Bool.and_eq_true] at hc
    have hK := hD.kTH k (ISub.id k) (by rw [I_subst_id hφs]; exact hn)
    rw [isub_id_of_closed hc.1.2] at hK
    exact kanH_retype hW (.inr ⟨lG, EqTm.glueFace (entails_of_holds hφs hn) hG⟩) hK ψ u u0 hty hu hu0
  have eq := EqTm.hcompGlue hty hAt he
  rw [hcompGlue_eq] at eq
  have hg := HasTy.eqR eq
  obtain ⟨htc0, hbase0, htube0, -, -⟩ := hcompGlue_parts hS (spec_to_minimal hW hty) (spec_to_minimal hW hG)
  obtain ⟨-, ⟨-, hψs, -, -, -⟩, -⟩ := gen_hcomp (spec_to_minimal hW hty) rfl
  have hGρ : ∀ k' (ρ : ISub k' k), HasTy S k' .one [] (.glue (A.isub ρ) (φ.subst ρ.τ) (T.isub ρ) (e.isub ρ)) (.univ lG) :=
    fun k' ρ => HasTy.isubS hW hG ρ
  have heqv : ∀ k' (ρ : ISub k' k) k'' (σ' : ISub k'' k'), (ival (idEnv k'') ((φ.subst ρ.τ).subst σ'.τ)).holds →
      RE S k'' (Tm.equiv ((T.isub ρ).isub σ') ((A.isub ρ).isub σ')) ((e.isub ρ).isub σ') := by
    intro k' ρ k'' σ' hh
    rw [Tm.isub_isub, Tm.isub_isub, Tm.isub_isub]
    rw [I_subst_subst] at hh
    exact hD.eqv k'' (ρ.comp σ') hh
  have hung : ∀ k' (ρ : ISub k' k) g, RE S k' (.glue (A.isub ρ) (φ.subst ρ.τ) (T.isub ρ) (e.isub ρ)) g →
      RE S k' (A.isub ρ) (.unglue (φ.subst ρ.τ) (e.isub ρ) g) :=
    fun k' ρ g hg => RE_unglue_gen hW hGC (hGρ k' ρ) (heqv k' ρ) hg
  have hGT : ∀ k' (ρ : ISub k' k), (ival (idEnv k') (φ.subst ρ.τ)).holds →
      EqTm S k' .one [] ((Tm.glue A φ T e).isub ρ) (T.isub ρ) (.univ lG) := fun k' ρ hh =>
    EqTm.glueFace (entails_of_holds (I.scoped_subst hφs ρ.sc) hh) (hGρ k' ρ)
  have hfib : ∀ k' (ρ : ISub k' k), (ival (idEnv k') (φ.subst ρ.τ)).holds →
      HasTy S k' .one [] (.hcomp (T.isub ρ) (ψ.subst ρ.τ) (u.isub ρ.up) (u0.isub ρ)) (T.isub ρ) ∧
      TubeC S k' (T.isub ρ) (ψ.subst ρ.τ) (u.isub ρ.up) ∧ RE S k' (T.isub ρ) (u0.isub ρ) := by
    intro k' ρ hh
    have hent := entails_of_holds (I.scoped_subst hφs ρ.sc) hh
    refine ⟨?_, fun k'' σ' r hr hh' => ?_, (hu0.isub hW ρ).conv_ty hW (.inr ⟨lG, hGT k' ρ hh⟩)⟩
    · have := HasTy.isubF hW (show (cof .one φ).Scoped k from ⟨trivial, hφs⟩) (minimal_to_spec htc0) ρ
      exact HasTy.restrict (show I.Scoped k' I.one from trivial) (ent_cof_one hW hent) this
    · have h1 := (hu.isub ρ) k'' σ' r hr hh'
      have e1 := EqTm.isubS hW (hGT k' ρ hh) σ'
      exact h1.conv_ty hW (.inr ⟨lG, e1⟩)
  refine (RE_glueEl_intro hW hG hn hg (fun k' σ => ?_) (fun k' σ hh => ?_)).conv hW (TyEq.refl _) eq.symm
  · refine hD.kA.1 k' σ _ _ _ (HasTy.isubS hW (minimal_to_spec hbase0) σ) ?_ (hung k' σ _ (hu0.isub hW σ))
    intro k'' σ' r hr hh
    change RE S k'' ((A.isub σ).isub σ') ((((Meta.glueTube φ T e ψ u u0).isub σ.up).isub σ'.up).dinst r)
    rw [Tm.isub_isub, Tm.isub_isub, ← ISub.up_comp]
    have hh' : (ival (idEnv k'') ((I.or ψ φ).subst (σ.comp σ').τ)).holds := by
      rw [show (I.or ψ φ).subst (σ.comp σ').τ = ((I.or ψ φ).subst σ.τ).subst σ'.τ from (I_subst_subst _ _ _).symm]
      exact hh
    generalize σ.comp σ' = ρ at hh' ⊢
    have hsp := HasTy.isubF hW (show (cof .one (I.or ψ φ)).shift.Scoped (k + 1) from
      I.scoped_shift ⟨trivial, hψs, hφs⟩) (minimal_to_spec htube0) (ISub.cons r hr ρ)
    rw [← isub_up_dinst, dshift_isub_cons] at hsp
    have hcf : (cof .one (I.or ψ φ)).shift.subst (ISub.cons r hr ρ).τ = cof .one ((I.or ψ φ).subst ρ.τ) :=
      I_shift_cons _ r hr ρ
    rw [hcf] at hsp
    have hsp' := HasTy.restrict (show I.Scoped k'' I.one from trivial) (ent_cof_one hW (entails_of_holds
      (I.scoped_subst (show (I.or ψ φ).Scoped k from ⟨hψs, hφs⟩) ρ.sc) hh')) hsp
    rw [glueTube_isub, glueTube_d] at hsp' ⊢
    rcases holds_or hh' with hψρ | hφρ
    · have e1 := EqTm.splitL (entails_of_holds (I.scoped_subst hψs ρ.sc) hψρ) hsp'
      exact (hung k'' ρ _ (hu k'' ρ r hr hψρ)).conv hW (TyEq.refl _) e1.symm
    · have e1 := EqTm.splitR (entails_of_holds (I.scoped_subst hφs ρ.sc) hφρ) hsp'
      obtain ⟨h1, h2, h3⟩ := hfib k'' ρ hφρ
      have hK : ∀ k3 (σ3 : ISub k3 k''), KanH S k3 ((T.isub ρ).isub σ3) := fun k3 σ3 => by
        rw [Tm.isub_isub]; exact hD.kTH k3 (ρ.comp σ3) (holds_restr hφs ρ σ3 hφρ)
      have hfl := RE_hfill hW hK h1 h2 h3
      have hflr := hfl.isub hW (ISub.cons r hr (ISub.id k''))
      rw [dshift_isub_cons, isub_id_of_closed (closed_of_isTyK hW (isTyK_of_ty hW h1)),
        isub_cons_id_dinst hW (closed_of_ty hW (Comp_el_typed hfl).1)] at hflr
      have hE := hD.eqv k'' ρ hφρ
      unfold Tm.equiv at hE
      have happ := RE_pi_elim hW (RE_sigma_elim hW hE).1 hflr
      rw [shift_inst] at happ
      exact happ.conv hW (TyEq.refl _) e1.symm
  · exact hD.kTH k' σ hh _ _ _ (hfib k' σ hh).1 (hfib k' σ hh).2.1 (hfib k' σ hh).2.2

omit hW in
theorem rt_of_comp {X : V} {g : Hom k m} {T : Tm} (h : (Comp S X m k g).ty T) : RT S k T := by
  unfold RT; rw [← Comp_eq_semK h]; exact h

theorem goodR_of_comp {X : V} (hX : KR S m X) {g : Hom k m} {T : Tm} (h : (Comp S X m k g).ty T) :
    GoodR S k (fun k' σ => (Comp S X m k' (g.comp σ.hom)).el) T := by
  intro k' σ Z t hZ
  have h1 := (hX k g k' σ T T).1 h
  show (Comp S X m k' (g.comp σ.hom)).el Z t ↔ (Comp S (semK S k' Z) k' k' (Hom.id k')).el Z t
  rw [Comp_eq_semK h1, semK_tyEq hW hZ]

/-- The computability data of a type of a Glue code whose face does not hold. -/
theorem glueL_of_comp {A Tp ep : V} {φ : Cof m} (hA : IsKV m A) (hφ : φ.IsCof)
    (hTp : ∀ k (f : Hom k m), (φ.restr f).holds → ∀ n (h : Hom n k), res h (dat Tp k f) = dat Tp n (f.comp h))
    (hTkv : ∀ k (f : Hom k m), (φ.restr f).holds → IsKV k (dat Tp k f))
    (hKA : KR S m A) (ihA : KanP S m A)
    (ihT : ∀ k (f : Hom k m), (φ.restr f).holds → KR S k (dat Tp k f) ∧ KanP S k (dat Tp k f))
    {n : ℕ} {f : Hom n m} (hf : ¬ (φ.restr f).holds) {T : Tm} (hT : (Comp S (glueC m A φ Tp ep) m n f).ty T) :
    ∃ A1 φ1 T1 e1, TyEq S n T (.glue A1 φ1 T1 e1) ∧ GlueL S n A1 φ1 T1 e1 := by
  rw [Comp_glueC_at hφ hTp hTkv f, if_neg hf, Comp_glueC (isKV_res _ _) (isKV_res _ _) (hφ.restr f) hf] at hT
  simp only [Comp_res (IsKV.ne_empty hA), dat_res, Cof.restr_restr] at hT
  obtain ⟨⟨hTy, -⟩, A1, φ1, T1, e1, hE, hs, hfc, hdata, hall1, hall2⟩ := hT
  have hface : ∀ k' (σ : ISub k' n), (ival (idEnv k') (φ1.subst σ.τ)).holds → (φ.restr (f.comp σ.hom)).holds :=
    fun k' σ hh => by rw [DM.holds_iff_face_holds, face_isub hfc σ, Cof.restr_restr] at hh; exact hh
  obtain ⟨lG, hG | hG⟩ := hTy.of_tyEq hE
  swap; · cases hG
  have hc := closed_of_ty hW hG
  simp only [Tm.closedB, Bool.and_eq_true] at hc
  refine ⟨A1, φ1, T1, e1, hE, ⟨lG, hG⟩, fun k' σ => rt_of_comp (hall1 k' σ), ?_,
    fun k' σ hh => rt_of_comp (hall2 k' σ (hface k' σ hh)).1,
    fun k' σ hh => (ihT k' _ (hface k' σ hh)).2.1 k' (Hom.id k') _ (hall2 k' σ (hface k' σ hh)).1,
    fun k' σ hh => (ihT (k' + 1) _ (hface (k' + 1) σ hh)).2.2 k' (Hom.id (k' + 1)) _ (hall2 (k' + 1) σ (hface _ σ hh)).1,
    fun k' σ hh => ?_⟩
  · have := kanAll_of hW hKA ihA (hall1 n (ISub.id n))
    rwa [isub_id_of_closed hc.1.1.1] at this
  · obtain ⟨h1, h2⟩ := hall2 k' σ (hface k' σ hh)
    obtain ⟨-, -, heσ⟩ := glue_fiber_ty hW hG σ hh
    obtain ⟨lE, hEt⟩ := ty_of_tyEq hW (isTyK_of_ty hW heσ) (TyEq.refl _) (fun l h => by cases h)
    have hGT := goodR_of_comp hW (ihT k' _ (hface k' σ hh)).1 h1
    have hGA := goodR_of_comp hW hKA (hall1 k' σ)
    simp only [Hom.id_comp] at hGT
    simp only [ISub.comp_hom] at hGA
    exact (goodR_equivE hW hEt hGT hGA k' (ISub.id k') _ _
      (by rw [isub_id_of_closed (closed_of_ty hW hEt)]; exact TyEq.refl _)).1 h2

end

end Model.Canon
