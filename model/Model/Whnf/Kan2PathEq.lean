import Model.Whnf.Kan2IPi

/-!
# Judgmental equality of the tubes of compositions in path types
-/

set_option autoImplicit false

namespace KubusCore.Meta

open Tm

variable {S : Sig}

theorem hcompPath_sys (hS : SigClosed S) {Ψ Φ Γ A a b φ u p0 T}
    (h : HasTy0 S Ψ Φ Γ (hcomp (path A a b) φ u p0) T) :
    HasTy0 S (Ψ + 1 + 1) (cof Φ.shift (.or φ.shift (.or (.neg (.var 0)) (.var 0)))).shift Γ.dshift.dshift
      (split φ.shift.shift (papp (u.dsubst insI) (.var 1)) (.or (.neg (.var 1)) (.var 1))
        (split (.neg (.var 1)) a.dshift.dshift (.var 1) b.dshift.dshift)) A.dshift := by
  obtain ⟨l, ⟨hP, hφ, hu, hp0, hside⟩, ch⟩ := gen_hcomp h rfl
  have hs := scoped_of_ty h
  have hw0 := wf_of_ty h
  have hA := HasTy0.pathLine hS hP
  have ha := HasTy0.pathLeft hS hP
  have hb := HasTy0.pathRight hS hP
  -- contexts
  let ψ : I := .or φ.shift (.or (.neg (.var 0)) (.var 0))
  have hψs : ψ.Scoped (Ψ + 1) := ⟨scoped_shift hφ, ⟨show 0 < Ψ + 1 by omega, show 0 < Ψ + 1 by omega⟩⟩
  have hΞs : (cof Φ.shift ψ).Scoped (Ψ + 1) := ⟨scoped_shift hs, hψs⟩
  have hR2s : (cof Φ.shift ψ).shift.Scoped (Ψ + 1 + 1) := scoped_shift hΞs
  have hφ2 : φ.shift.shift.Scoped (Ψ + 1 + 1) := scoped_shift (scoped_shift hφ)
  have hv1 : (I.var 1).Scoped (Ψ + 1 + 1) := show 1 < Ψ + 1 + 1 by omega
  have hv0 : (I.var 0).Scoped (Ψ + 1 + 1) := show 0 < Ψ + 1 + 1 by omega
  let ψ2 : I := .or (.neg (.var 1)) (.var 1)
  have hψ2s : ψ2.Scoped (Ψ + 1 + 1) := ⟨hv1, hv1⟩
  -- the line in the tube context
  have hA2 : HasTy0 S (Ψ + 1 + 1) (cof Φ.shift ψ).shift Γ.dshift.dshift A.dshift (univ l) :=
    HasTy0.restrict hR2s (ent_shift (ent_and_left _ _)) (HasTy0.dwk hS hA)
  -- the tube
  have hu2 := tube_skip hS hu
  rw [path_dshift_skip] at hu2
  have hU := HasTy0.papp hu2 hv1
  rw [Xp_var1] at hU
  have hR3 : (cof (cof Φ.shift ψ).shift φ.shift.shift).Scoped (Ψ + 1 + 1) := ⟨hR2s, hφ2⟩
  have hR3e : I.Entails (cof (cof Φ.shift ψ).shift φ.shift.shift) (cof Φ φ).shift.shift :=
    ent_and_mono (ent_shift (ent_and_left Φ.shift ψ)) (ent_refl _)
  have hUr := HasTy0.restrict hR3 hR3e hU
  -- the inner system `[j = 0 ↦ a, j = 1 ↦ b]`
  have hR2Φ : I.Entails (cof Φ.shift ψ).shift Φ.shift.shift := ent_shift (ent_and_left Φ.shift ψ)
  have hΞ2s : (cof (cof Φ.shift ψ).shift ψ2).Scoped (Ψ + 1 + 1) := ⟨hR2s, hψ2s⟩
  have hXa : (cof (cof (cof Φ.shift ψ).shift ψ2) (.neg (.var 1))).Scoped (Ψ + 1 + 1) := ⟨hΞ2s, hv1⟩
  have hXb : (cof (cof (cof Φ.shift ψ).shift ψ2) (.var 1)).Scoped (Ψ + 1 + 1) := ⟨hΞ2s, hv1⟩
  have hXaΦ : I.Entails (cof (cof (cof Φ.shift ψ).shift ψ2) (.neg (.var 1))) (cof Φ.shift ψ).shift :=
    ent_trans (ent_and_left _ _) (ent_and_left _ _)
  have hXbΦ : I.Entails (cof (cof (cof Φ.shift ψ).shift ψ2) (.var 1)) (cof Φ.shift ψ).shift :=
    ent_trans (ent_and_left _ _) (ent_and_left _ _)
  have ha2 : HasTy0 S (Ψ + 1 + 1) (cof (cof (cof Φ.shift ψ).shift ψ2) (.neg (.var 1))) Γ.dshift.dshift
      a.dshift.dshift A.dshift := by
    have h1 := HasTy0.restrict hXa (ent_trans hXaΦ hR2Φ) (HasTy0.dwk hS (HasTy0.dwk hS ha))
    have hf := EqTm0.faceU (i := 1) (d := false) hv1 (ent_and_right _ _) (HasTy0.restrict hXa hXaΦ hA2)
    rw [dshift_dset1_zero] at hf
    exact HasTy0.conv h1 (EqTm0.symm hf)
  have hb2 : HasTy0 S (Ψ + 1 + 1) (cof (cof (cof Φ.shift ψ).shift ψ2) (.var 1)) Γ.dshift.dshift
      b.dshift.dshift A.dshift := by
    have h1 := HasTy0.restrict hXb (ent_trans hXbΦ hR2Φ) (HasTy0.dwk hS (HasTy0.dwk hS hb))
    have hf := EqTm0.faceU (i := 1) (d := true) hv1 (ent_and_right _ _) (HasTy0.restrict hXb hXbΦ hA2)
    rw [dshift_dset1_one] at hf
    exact HasTy0.conv h1 (EqTm0.symm hf)
  have hXab : (cof (cof (cof (cof Φ.shift ψ).shift ψ2) (.neg (.var 1))) (.var 1)).Scoped (Ψ + 1 + 1) :=
    ⟨hXa, hv1⟩
  have hinner : HasTy0 S (Ψ + 1 + 1) (cof (cof Φ.shift ψ).shift ψ2) Γ.dshift.dshift
      (split (.neg (.var 1)) a.dshift.dshift (.var 1) b.dshift.dshift) A.dshift :=
    HasTy0.split hv1 hv1 (ent_and_right _ _) (HasTy0.restrict hΞ2s (ent_and_left _ _) hA2) ha2 hb2
      (EqTm0.absurd (ent_contra _ 1) (HasTy0.restrict hXab (ent_and_left _ _) ha2)
        (HasTy0.restrict hXab (ent_and_mono (ent_and_left _ _) (ent_refl _)) hb2))
  -- agreement of the tube with the inner system
  have hY : (cof (cof (cof Φ.shift ψ).shift φ.shift.shift) ψ2).Scoped (Ψ + 1 + 1) := ⟨hR3, hψ2s⟩
  have hover : EqTm0 S (Ψ + 1 + 1) (cof (cof (cof Φ.shift ψ).shift φ.shift.shift) ψ2) Γ.dshift.dshift
      (papp (u.dsubst insI) (.var 1)) (split (.neg (.var 1)) a.dshift.dshift (.var 1) b.dshift.dshift)
      A.dshift := by
    have hYU := HasTy0.restrict hY (ent_and_left _ _) hUr
    have hYI := HasTy0.restrict hY (ent_and_mono (ent_and_left _ _) (ent_refl _)) hinner
    have hYA := HasTy0.restrict hY (ent_trans (ent_and_left _ _) (ent_and_left _ _)) hA2
    have hpu := HasTy0.restrict hY (ent_trans (ent_and_left _ _) hR3e) hu2
    refine EqTm0.local (φ := .neg (.var 1)) (ψ := .var 1) hv1 hv1 (ent_and_right _ _) hYU hYI ?_ ?_
    · have hs1 : (cof (cof (cof (cof Φ.shift ψ).shift φ.shift.shift) ψ2) (.neg (.var 1))).Scoped (Ψ + 1 + 1) :=
        ⟨hY, hv1⟩
      have e1 := EqTm0.face (i := 1) (d := false) hv1 (ent_and_right _ _)
        (HasTy0.restrict hs1 (ent_and_left _ _) hYA) (HasTy0.restrict hs1 (ent_and_left _ _) hYU)
      rw [papp_insI_dset1] at e1
      have e2 := EqTm0.pathZero (HasTy0.restrict hs1 (ent_and_left _ _) hpu)
      rw [Xp_zero] at e2
      have hf := EqTm0.faceU (i := 1) (d := false) hv1 (ent_and_right _ _)
        (HasTy0.restrict hs1 (ent_and_left _ _) hYA)
      rw [dshift_dset1_zero] at hf
      have e3 := EqTm0.splitL (ent_and_right _ _) (HasTy0.restrict hs1 (ent_and_left _ _) hYI)
      exact EqTm0.trans e1 (EqTm0.trans (EqTm0.conv e2 (EqTm0.symm hf)) (EqTm0.symm e3))
    · have hs1 : (cof (cof (cof (cof Φ.shift ψ).shift φ.shift.shift) ψ2) (.var 1)).Scoped (Ψ + 1 + 1) :=
        ⟨hY, hv1⟩
      have e1 := EqTm0.face (i := 1) (d := true) hv1 (ent_and_right _ _)
        (HasTy0.restrict hs1 (ent_and_left _ _) hYA) (HasTy0.restrict hs1 (ent_and_left _ _) hYU)
      rw [papp_insI_dset1] at e1
      have e2 := EqTm0.pathOne (HasTy0.restrict hs1 (ent_and_left _ _) hpu)
      rw [Xp_one] at e2
      have hf := EqTm0.faceU (i := 1) (d := true) hv1 (ent_and_right _ _)
        (HasTy0.restrict hs1 (ent_and_left _ _) hYA)
      rw [dshift_dset1_one] at hf
      have e3 := EqTm0.splitR (ent_and_right _ _) (HasTy0.restrict hs1 (ent_and_left _ _) hYI)
      exact EqTm0.trans e1 (EqTm0.trans (EqTm0.conv e2 (EqTm0.symm hf)) (EqTm0.symm e3))
  have hsys : HasTy0 S (Ψ + 1 + 1) (cof Φ.shift ψ).shift Γ.dshift.dshift
      (split φ.shift.shift (papp (u.dsubst insI) (.var 1)) ψ2
        (split (.neg (.var 1)) a.dshift.dshift (.var 1) b.dshift.dshift)) A.dshift :=
    HasTy0.split hφ2 hψ2s (ent_shift (ent_and_right Φ.shift ψ)) hA2 hUr hinner hover
  exact hsys

/-- The tubes of compositions in path types, with judgmentally equal data, are judgmentally equal. -/
theorem hcompPath_sys_eq (hW : WfSig S) {Ψ : Nat} {A A' a a' b b' u u' p0 p0' T T' : Tm} {φ φ' : I} {l : Nat}
    (h : HasTy0 S Ψ .one [] (hcomp (path A a b) φ u p0) T)
    (h' : HasTy0 S Ψ .one [] (hcomp (path A' a' b') φ' u' p0') T')
    (hAA : EqTm0 S (Ψ + 1) .one [] A A' (univ l))
    (haa : EqTm0 S Ψ .one [] a a' (A.dinst .zero)) (hbb : EqTm0 S Ψ .one [] b b' (A.dinst .one))
    (huu : EqTm0 S (Ψ + 1) (cof .one φ).shift [] u u' (path A a b).dshift)
    (h12 : I.Entails φ φ') :
    EqTm0 S (Ψ + 1 + 1) (cof I.one.shift (.or φ.shift (.or (.neg (.var 0)) (.var 0)))).shift []
      (split φ.shift.shift (papp (u.dsubst insI) (.var 1)) (.or (.neg (.var 1)) (.var 1))
        (split (.neg (.var 1)) a.dshift.dshift (.var 1) b.dshift.dshift))
      (split φ'.shift.shift (papp (u'.dsubst insI) (.var 1)) (.or (.neg (.var 1)) (.var 1))
        (split (.neg (.var 1)) a'.dshift.dshift (.var 1) b'.dshift.dshift)) A.dshift := by
  have hS := sigClosed_of_wfSig hW
  have hsL := hcompPath_sys hS h
  have hsR := hcompPath_sys hS h'
  obtain ⟨l1, ⟨hP, hφ, -, -, -⟩, -⟩ := gen_hcomp h rfl
  obtain ⟨l2, ⟨-, hφ', -, -, -⟩, -⟩ := gen_hcomp h' rfl
  have hv1 : (I.var 1).Scoped (Ψ + 1 + 1) := show 1 < Ψ + 1 + 1 by omega
  have hv0 : (I.var 0).Scoped (Ψ + 1) := show 0 < Ψ + 1 by omega
  let ψ : I := .or φ.shift (.or (.neg (.var 0)) (.var 0))
  let ψ' : I := .or φ'.shift (.or (.neg (.var 0)) (.var 0))
  let ψ2 : I := .or (.neg (.var 1)) (.var 1)
  have hψs : ψ.Scoped (Ψ + 1) := ⟨scoped_shift hφ, ⟨hv0, hv0⟩⟩
  have hC2 : (cof I.one.shift ψ).shift.Scoped (Ψ + 1 + 1) := scoped_shift ⟨trivial, hψs⟩
  have hφ2 : φ.shift.shift.Scoped (Ψ + 1 + 1) := scoped_shift (scoped_shift hφ)
  have hψ2s : ψ2.Scoped (Ψ + 1 + 1) := ⟨hv1, hv1⟩
  -- the right system in the left context, at the left type
  have hCC : I.Entails (cof I.one.shift ψ).shift (cof I.one.shift ψ').shift :=
    ent_shift (ent_and_mono (ent_refl _) (ent_or_elim (ent_trans (ent_shift h12) (ent_or_left _ _))
      (ent_or_right _ _)))
  have eA := EqTm0.restrict hC2 (ent_one _) (EqTm0.dwk hS hAA)
  have hsR' := HasTy0.conv (HasTy0.restrict hC2 hCC hsR) (EqTm0.symm eA)
  refine EqTm0.local (φ := φ.shift.shift) (ψ := ψ2) hφ2 hψ2s (ent_trans (ent_and_right _ _) (ent_refl _))
    hsL hsR' ?_ ?_
  · -- the tubes
    have hc : (cof (cof I.one.shift ψ).shift φ.shift.shift).Scoped (Ψ + 1 + 1) := ⟨hC2, hφ2⟩
    have s1 := EqTm0.splitL (ent_and_right _ _) (HasTy0.restrict hc (ent_and_left _ _) hsL)
    have s2 := EqTm0.splitL (ent_trans (ent_and_right _ _) (ent_shift (ent_shift h12)))
      (HasTy0.restrict hc (ent_and_left _ _) hsR')
    have hI := EqTm0.isub hS huu (Ψ' := Ψ + 1 + 1) (Φ' := cof (cof I.one.shift ψ).shift φ.shift.shift)
      (τ := rI skip1) (fun i hi => by rcases i with _ | i <;> simp [rI, skip1, I.Scoped] <;> omega)
      (by
        show I.Entails _ (I.and (I.one.shift.subst (rI skip1)) (φ.shift.subst (rI skip1)))
        refine ent_and_intro (ent_one _) (ent_trans (ent_and_right _ _) (eq_ent ?_))
        intro ρ; simp only [I.shift, I.ren, eval_subst]; rfl)
      (Wf0.nil hc)
    have hI' : EqTm0 S (Ψ + 1 + 1) (cof (cof I.one.shift ψ).shift φ.shift.shift) []
        (u.subst (rS id) (rI skip1)) (u'.subst (rS id) (rI skip1)) ((path A a b).dshift.subst (rS id) (rI skip1)) := hI
    rw [insI_eq, insI_eq, path_dshift_skip] at hI'
    have m := EqTm0.papp hI' hv1 hv1 (I_eq_refl _)
    rw [Xp_var1] at m
    exact EqTm0.trans s1 (EqTm0.trans m (EqTm0.symm s2))
  · -- the endpoints
    have hc : (cof (cof I.one.shift ψ).shift ψ2).Scoped (Ψ + 1 + 1) := ⟨hC2, hψ2s⟩
    have t1 := EqTm0.splitR (ent_and_right _ _) (HasTy0.restrict hc (ent_and_left _ _) hsL)
    have t2 := EqTm0.splitR (ent_and_right _ _) (HasTy0.restrict hc (ent_and_left _ _) hsR')
    have hinL := spec_to_minimal hW (HasTy.eqR (minimal_to_spec_eq t1))
    have hinR := spec_to_minimal hW (HasTy.eqR (minimal_to_spec_eq t2))
    have hA := HasTy0.pathLine hS hP
    have hA2 : ∀ {Φ' : I}, Φ'.Scoped (Ψ + 1 + 1) → HasTy0 S (Ψ + 1 + 1) Φ' [] A.dshift (univ l1) :=
      fun hs => HasTy0.restrict hs (ent_one _) (HasTy0.dwk hS hA)
    have ea : ∀ (d : Bool) {x x' : Tm}, EqTm0 S Ψ .one [] x x' (A.dinst (I.ofDir d)) →
        EqTm0 S (Ψ + 1 + 1) (cof (cof (cof I.one.shift ψ).shift ψ2) (I.lit 1 d)) [] x.dshift.dshift x'.dshift.dshift
          A.dshift := by
      intro d x x' hx
      have hc3 : (cof (cof (cof I.one.shift ψ).shift ψ2) (I.lit 1 d)).Scoped (Ψ + 1 + 1) := ⟨hc, by cases d <;> exact hv1⟩
      have e := EqTm0.restrict hc3 (ent_one _) (EqTm0.dwk hS (EqTm0.dwk hS hx))
      have hf := EqTm0.faceU (i := 1) (d := d) (by omega) (ent_and_right _ _) (hA2 hc3)
      cases d
      · rw [dshift_dset1_zero] at hf; exact EqTm0.conv e (EqTm0.symm hf)
      · rw [dshift_dset1_one] at hf; exact EqTm0.conv e (EqTm0.symm hf)
    have m := EqTm0.split hinL hinR (ea false haa) (ea true hbb)
    exact EqTm0.trans t1 (EqTm0.trans m (EqTm0.symm t2))

theorem ieq_neg {x x' : I} (h : I.Eq x x') : I.Eq (.neg x) (.neg x') := fun ρ => by
  simp only [I.eval]; rw [h ρ]

theorem ent_or3 {φ φ' x x' : I} (h : I.Entails φ φ') (e : I.Eq x x') :
    I.Entails (.or φ (.or (.neg x) x)) (.or φ' (.or (.neg x') x')) :=
  ent_or_elim (ent_trans h (ent_or_left _ _))
    (ent_trans (ent_or_elim (ent_trans (eq_ent (ieq_neg e)) (ent_or_left _ _))
      (ent_trans (eq_ent e) (ent_or_right _ _))) (ent_or_right _ _))

theorem sysJ_inst (a b u : Tm) (φ r : I) :
    (split φ.shift.shift (papp (u.dsubst insI) (.var 1)) (.or (.neg (.var 1)) (.var 1))
        (split (.neg (.var 1)) a.dshift.dshift (.var 1) b.dshift.dshift)).subst Tm.var (I.up (I.inst0 r)) =
      split φ.shift (papp u r.shift) (.or (.neg r.shift) r.shift) (split (.neg r.shift) a.dshift r.shift b.dshift) := by
  have hφ : φ.shift.shift.subst (I.up (I.inst0 r)) = φ.shift := by
    rw [I_shift_subst_up, Model.Canon.I_shift_inst0]
  have hd : ∀ x : Tm, x.dshift.dshift.subst Tm.var (I.up (I.inst0 r)) = x.dshift := by
    intro x; simp only [dshift_eq, subst_subst]
    exact subst_congr (fun _ => rfl) (fun i => rfl) x
  have hu : (u.dsubst insI).subst Tm.var (I.up (I.inst0 r)) = u := by
    simp only [Tm.dsubst, subst_subst]
    exact subst_id_of (fun _ => rfl) (fun i => by rcases i with _ | i <;> rfl) u
  simp only [Tm.subst, I.subst]
  rw [hφ, hd a, hd b, hu]
  rfl

theorem dshift_up_inst0 (A : Tm) (r : I) : A.dshift.subst Tm.var (I.up (I.inst0 r)) = (A.dinst r).dshift := by
  simp only [dshift_eq, Tm.dinst, Tm.dsubst, subst_subst]
  exact subst_congr (fun _ => rfl) (fun i => by rcases i with _ | i <;> rfl) A

/-- The systems of the compositions at a point of a path type are judgmentally equal. -/
theorem hcompPath_sysr_eq (hW : WfSig S) {Ψ : Nat} {A A' a a' b b' u u' p0 p0' T T' : Tm} {φ φ' r r' : I}
    (h : HasTy0 S Ψ .one [] (hcomp (path A a b) φ u p0) T)
    (h' : HasTy0 S Ψ .one [] (hcomp (path A' a' b') φ' u' p0') T')
    (hPP : path A a b = path A' a' b' ∨ ∃ l, EqTm0 S Ψ .one [] (path A a b) (path A' a' b') (univ l))
    (huu : EqTm0 S (Ψ + 1) (cof .one φ).shift [] u u' (path A a b).dshift)
    (h12 : I.Entails φ φ') (hr : r.Scoped Ψ) (hr' : r'.Scoped Ψ) (hE : I.Eq r r') :
    EqTm0 S (Ψ + 1) (cof .one (.or φ (.or (.neg r) r))).shift []
      (split φ.shift (papp u r.shift) (.or (.neg r.shift) r.shift) (split (.neg r.shift) a.dshift r.shift b.dshift))
      (split φ'.shift (papp u' r'.shift) (.or (.neg r'.shift) r'.shift)
        (split (.neg r'.shift) a'.dshift r'.shift b'.dshift)) (A.dinst r).dshift := by
  have hS := sigClosed_of_wfSig hW
  obtain ⟨l1, ⟨hP, hφ, -, -, -⟩, -⟩ := gen_hcomp h rfl
  obtain ⟨l2, ⟨hP', hφ', -, -, -⟩, -⟩ := gen_hcomp h' rfl
  have hA := HasTy0.pathLine hS hP
  -- the components of the path types
  have comps : ∃ l, EqTm0 S (Ψ + 1) .one [] A A' (univ l) ∧ EqTm0 S Ψ .one [] a a' (A.dinst .zero) ∧
      EqTm0 S Ψ .one [] b b' (A.dinst .one) ∧ EqTm0 S Ψ .one [] (A.dinst r) (A'.dinst r) (univ l) := by
    rcases hPP with e | ⟨l, e⟩
    · injection e with e1 e2 e3; subst e1 e2 e3
      exact ⟨l1, EqTm0.refl hA, EqTm0.refl (HasTy0.pathLeft hS hP), EqTm0.refl (HasTy0.pathRight hS hP),
        EqTm0.dsubst hS (Φ := .one) (Γ := []) (EqTm0.refl hA) hr⟩
    · have ed := EqTm0.restrict (Φ' := .one) trivial (ent_one _) (EqTm0.dwk hS e)
      have el := EqTm0.pathInjLine (A := A.ren id (upRen Nat.succ)) (A' := A'.ren id (upRen Nat.succ))
        (r := .var 0) ed (show 0 < Ψ + 1 by omega)
      rw [upDShift_dinst0, upDShift_dinst0] at el
      exact ⟨l, el, EqTm0.pathInjLeft e, EqTm0.pathInjRight e, EqTm0.pathInjLine e hr⟩
  obtain ⟨l, hAA, haa, hbb, hAr⟩ := comps
  have E := hcompPath_sys_eq hW h h' hAA haa hbb huu h12
  have hsR := hcompPath_sys hS h'
  have hΦs : (cof I.one (.or φ (.or (.neg r) r))).shift.Scoped (Ψ + 1) := scoped_shift ⟨trivial, ⟨hφ, ⟨hr, hr⟩⟩⟩
  have hb : ∀ (x : I), x.Scoped Ψ → ∀ i < Ψ + 1 + 1, ((I.up (I.inst0 x)) i).Scoped (Ψ + 1) := by
    intro x hx i hi
    rcases i with _ | _ | i
    · show 0 < Ψ + 1; omega
    · exact scoped_shift hx
    · show i + 1 < Ψ + 1; omega
  have hC : ∀ (x : I) (χ : I), ((cof I.one.shift (.or χ.shift (.or (.neg (.var 0)) (.var 0)))).shift.subst
      (I.up (I.inst0 x))) = (cof I.one (.or χ (.or (.neg x) x))).shift := by
    intro x χ
    rw [I_shift_subst_up]
    show I.shift (cof (I.one.shift.subst _) (.or (χ.shift.subst _) (.or (.neg x) x))) = _
    rw [Model.Canon.I_shift_inst0, Model.Canon.I_shift_inst0]
  have L : EqTm0 S (Ψ + 1) (cof I.one (.or φ (.or (.neg r) r))).shift [] _ _ _ :=
    EqTm0.isub hS E (hb r hr) (by rw [hC]; exact ent_refl _) (Wf0.nil hΦs)
  rw [sysJ_inst, sysJ_inst, dshift_up_inst0] at L
  have R : EqTm0 S (Ψ + 1) (cof I.one (.or φ (.or (.neg r) r))).shift [] _ _ _ :=
    HasTy0.ieq hS hsR (hb r hr) (hb r' hr')
      (by rw [hC]; exact ent_shift (ent_and_mono (ent_refl _) (ent_or3 h12 (I_eq_refl _))))
      (by rw [hC]; exact ent_shift (ent_and_mono (ent_refl _) (ent_or3 h12 hE)))
      (fun i hi => by
        rcases i with _ | _ | i
        · exact I_eq_refl _
        · exact fun ρ0 => by simp only [I.up, I.inst0, I.shift, eval_ren]; exact hE _
        · exact I_eq_refl _) rfl (Wf0.nil hΦs)
  rw [sysJ_inst, sysJ_inst, dshift_up_inst0] at R
  have eA := EqTm0.restrict hΦs (ent_one _) (EqTm0.dwk hS hAr)
  exact EqTm0.trans L (EqTm0.conv R (EqTm0.symm eA))

/-- The tubes of related fillers are judgmentally equal. -/
theorem fillTube_eq (hW : WfSig S) {Ψ : Nat} {A A' u u' u0 u0' T T' : Tm} {φ φ' : I}
    (h : HasTy0 S (Ψ + 1) .one [] (hcomp A.dshift (.or φ.shift (.neg (.var 0))) (fillTube φ u u0) u0.dshift) T)
    (h' : HasTy0 S (Ψ + 1) .one [] (hcomp A'.dshift (.or φ'.shift (.neg (.var 0))) (fillTube φ' u' u0') u0'.dshift) T')
    (hAA : A = A' ∨ ∃ l, EqTm0 S Ψ .one [] A A' (univ l))
    (huu : EqTm0 S (Ψ + 1) (cof .one φ).shift [] u u' A.dshift) (hu0 : EqTm0 S Ψ .one [] u0 u0' A)
    (h12 : I.Entails φ φ') :
    EqTm0 S (Ψ + 1 + 1) (cof I.one (.or φ.shift (.neg (.var 0)))).shift [] (fillTube φ u u0) (fillTube φ' u' u0')
      A.dshift.dshift := by
  have hS := sigClosed_of_wfSig hW
  obtain ⟨l1, ⟨-, hψ, hsL, -, -⟩, -⟩ := gen_hcomp h rfl
  obtain ⟨l2, ⟨-, -, hsR, -, -⟩, -⟩ := gen_hcomp h' rfl
  have hC : (cof I.one (.or φ.shift (.neg (.var 0)))).shift.Scoped (Ψ + 1 + 1) := scoped_shift ⟨trivial, hψ⟩
  have hφ2 : φ.shift.shift.Scoped (Ψ + 1 + 1) := scoped_shift hψ.1
  have hv1 : (I.var 1).Scoped (Ψ + 1 + 1) := show 1 < Ψ + 1 + 1 by omega
  have hCC : I.Entails (cof I.one (.or φ.shift (.neg (.var 0)))).shift
      (cof I.one (.or φ'.shift (.neg (.var 0)))).shift :=
    ent_shift (ent_and_mono (ent_refl _) (ent_or_elim (ent_trans (ent_shift h12) (ent_or_left _ _))
      (ent_or_right _ _)))
  have hsR' : HasTy0 S (Ψ + 1 + 1) (cof I.one (.or φ.shift (.neg (.var 0)))).shift [] (fillTube φ' u' u0')
      A.dshift.dshift := by
    rcases hAA with rfl | ⟨l, e⟩
    · exact HasTy0.restrict hC hCC hsR
    · have eA := EqTm0.restrict hC (ent_one _) (EqTm0.dwk hS (EqTm0.dwk hS e))
      exact HasTy0.conv (HasTy0.restrict hC hCC hsR) (EqTm0.symm eA)
  refine EqTm0.local (φ := φ.shift.shift) (ψ := .neg (.var 1)) hφ2 hv1 (ent_trans (ent_and_right _ _) (ent_refl _))
    hsL hsR' ?_ ?_
  · have hc : (cof (cof I.one (.or φ.shift (.neg (.var 0)))).shift φ.shift.shift).Scoped (Ψ + 1 + 1) := ⟨hC, hφ2⟩
    have s1 := EqTm0.splitL (ent_and_right _ _) (HasTy0.restrict hc (ent_and_left _ _) hsL)
    have s2 := EqTm0.splitL (ent_trans (ent_and_right _ _) (ent_shift (ent_shift h12)))
      (HasTy0.restrict hc (ent_and_left _ _) hsR')
    have m : EqTm0 S (Ψ + 1 + 1) (cof (cof I.one (.or φ.shift (.neg (.var 0)))).shift φ.shift.shift) [] _ _ _ :=
      EqTm0.isub hS huu (τ := bind2 (.and (.var 1) (.var 0)))
        (fun i hi => by
          rcases i with _ | i
          · exact ⟨show 1 < Ψ + 1 + 1 by omega, show 0 < Ψ + 1 + 1 by omega⟩
          · show i + 2 < Ψ + 1 + 1; omega)
        (ent_bind2_shift _ (ent_and_intro (ent_one _) (ent_and_right _ _))) (Wf0.nil hc)
    rw [dshift_bind2] at m
    exact EqTm0.trans s1 (EqTm0.trans m (EqTm0.symm s2))
  · have hc : (cof (cof I.one (.or φ.shift (.neg (.var 0)))).shift (.neg (.var 1))).Scoped (Ψ + 1 + 1) := ⟨hC, hv1⟩
    have t1 := EqTm0.splitR (ent_and_right _ _) (HasTy0.restrict hc (ent_and_left _ _) hsL)
    have t2 := EqTm0.splitR (ent_and_right _ _) (HasTy0.restrict hc (ent_and_left _ _) hsR')
    have m := EqTm0.restrict hc (ent_one _) (EqTm0.dwk hS (EqTm0.dwk hS hu0))
    exact EqTm0.trans t1 (EqTm0.trans m (EqTm0.symm t2))

end KubusCore.Meta
