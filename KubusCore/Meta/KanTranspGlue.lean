import KubusCore.Meta.KanTranspGlueAux

/-!
# Metatheory: typing the contractum of `transp` in Glue types
-/

namespace KubusCore.Meta

open Tm

variable {S : Sig}

set_option linter.unusedSectionVars false

/-! ## The parts of the contractum -/

section
variable (A : Tm) (e : Tm) (ψ : I) (u0 : Tm) (F G : Tm)
def tgSys' : Tm :=
  split ψ.shift.shift (app (fst (e.dsubst (sk (.var 0) 2))) u0.dshift.dshift) (.or (.neg (.var 1)) (.var 1))
    (split (.neg (.var 1)) (app (fst (e.dsubst (sk (.var 0) 2))) (F.dsubst (sk (.var 0) 2)))
      (.var 1) (G.dsubst (sk (.var 0) 2)))
theorem L_C0 : (A.dsubst (sk (.var 0) 2)).dinst .zero = (A.dinst .zero).dshift := by ssub
theorem L_C1 : (A.dsubst (sk (.var 0) 2)).dinst .one = (A.dinst .one).dshift := by ssub
theorem L_CE (d : Bool) : (A.dsubst (sk (.var 0) 2)).subst Tm.var (endS d) = A.dinst .one := by cases d <;> ssub
theorem L_Cup (r : I) : (A.dsubst (sk (.var 0) 2)).subst Tm.var (I.up (I.inst0 r)) = A := by ssub
theorem sys_d (r : I) (hr : r = .zero ∨ r = .one) : (tgSys' e ψ u0 F G).dinst r =
    split ψ.shift (app (fst (e.dinst r).dshift) u0.dshift) (.or (.neg (.var 0)) (.var 0))
      (split (.neg (.var 0)) (app (fst (e.dinst r).dshift) (F.dinst r).dshift) (.var 0) (G.dinst r).dshift) := by
  rcases hr with rfl | rfl <;> (simp only [tgSys']; scalc)
theorem sys_end (d : Bool) : (tgSys' e ψ u0 F G).subst Tm.var (endS d) =
    split ψ (app (fst (e.dinst .one)) u0) (.or (.neg (I.ofDir d)) (I.ofDir d))
      (split (.neg (I.ofDir d)) (app (fst (e.dinst .one)) (F.dinst .one)) (I.ofDir d) (G.dinst .one)) := by
  simp only [tgSys', Tm.subst, shift2_endS]
  have h1 : ∀ X : Tm, (X.dsubst (sk (.var 0) 2)).subst Tm.var (endS d) = X.dinst .one := fun X => by
    cases d <;> ssub
  have h2 : u0.dshift.dshift.subst Tm.var (endS d) = u0 := dshift2_endS u0 d
  rw [h1, h1, h1, h2]
  rfl
end

section
variable (A : Tm) (φ : I) (T e : Tm) (ψ : I) (u0 : Tm) (δ : I)

def tgA0 : Tm := unglue (φ.subst (I.inst0 .zero)) (e.dinst .zero) u0
def tgTube : Tm := unglue φ e u0.dshift
def tgA1' : Tm := comp A ψ (tgTube φ e u0) (tgA0 φ e u0)
def tgT1 : Tm := transp T ψ u0
def tgSys : Tm := tgSys' e ψ u0 (transpFill T ψ u0) (fill A ψ (tgTube φ e u0) (tgA0 φ e u0))
def tgBody : Tm :=
  comp (A.dsubst (sk (.var 0) 2)) (.or ψ.shift (.or (.neg (.var 0)) (.var 0))) (tgSys A φ T e ψ u0)
    (app (fst (e.dinst .zero).dshift) u0.dshift)
def tgOmega : Tm := plam (tgBody A φ T e ψ u0)
def tgC : Tm := app (snd (e.dinst .one)) (tgA1' A φ e ψ u0)
def tgFib : Tm := fiber (T.dinst .one) (A.dinst .one) (fst (e.dinst .one)) (tgA1' A φ e ψ u0)
def tgPd : Tm := app (snd (tgC A φ e ψ u0)) (pair (tgT1 T ψ u0) (tgOmega A φ T e ψ u0))
def tgPpsi : Tm := app (snd (tgC A φ e ψ u0)) (pair u0 (plam (tgA1' A φ e ψ u0).dshift))
def tgExt : Tm :=
  hcomp (tgFib A φ T e ψ u0) (.or δ ψ)
    (split δ.shift (papp (tgPd A φ T e ψ u0).dshift (.var 0)) ψ.shift (papp (tgPpsi A φ e ψ u0).dshift (.var 0)))
    (fst (tgC A φ e ψ u0))
def tgA1 : Tm :=
  hcomp (A.dinst .one) (.or (φ.subst (I.inst0 .one)) ψ)
    (split (φ.subst (I.inst0 .one)).shift (papp (snd (tgExt A φ T e ψ u0 δ)).dshift (.neg (.var 0)))
      ψ.shift (tgA1' A φ e ψ u0).dshift) (tgA1' A φ e ψ u0)

theorem tgBody_dinst (r : I) : (tgBody A φ T e ψ u0).dinst r =
    comp A (.or ψ (.or (.neg r) r)) ((tgSys A φ T e ψ u0).subst Tm.var (I.up (I.inst0 r)))
      (app (fst (e.dinst .zero)) u0) := by
  show (comp _ _ _ _).subst Tm.var (I.inst0 r) = _
  rw [comp_substI, L_Cup]
  congr 1
  · show I.or (ψ.shift.subst (I.inst0 r)) _ = _
    simp only [I.shift, I.ren, I_subst_subst]; congr 1; exact I_subst_var ψ
  · show app (fst ((e.dinst .zero).dshift.dinst r)) (u0.dshift.dinst r) = _
    rw [dshift_dinst, dshift_dinst]

theorem plam_dshift_dshift (a : Tm) : (plam a.dshift).dshift = plam a.dshift.dshift := by
  show plam (a.dshift.ren id (upRen Nat.succ)) = _; congr 1; ssub

theorem transpGlueWith_eq : transpGlueWith δ A φ T e ψ u0 =
    glueEl (φ.subst (I.inst0 .one)) (e.dinst .one) (fst (tgExt A φ T e ψ u0 δ)) (tgA1 A φ T e ψ u0 δ) := by
  simp only [transpGlueWith, tgA1, tgExt, tgPd, tgPpsi, tgFib, tgC, tgOmega, tgBody, tgSys, tgSys', tgT1, tgA1',
    tgTube, tgA0]
  rw [← plam_dshift_dshift]
  rfl

end

theorem equiv_dinst (T A : Tm) (r : I) : (equiv T A).dinst r = equiv (T.dinst r) (A.dinst r) :=
  equiv_subst _ _ T A

theorem glue_dinst (A : Tm) (φ : I) (T e : Tm) (r : I) :
    (glue A φ T e).dinst r = glue (A.dinst r) (φ.subst (I.inst0 r)) (T.dinst r) (e.dinst r) := rfl

theorem tgTube_dinst (φ : I) (e u0 : Tm) (r : I) :
    (tgTube φ e u0).dinst r = unglue (φ.subst (I.inst0 r)) (e.dinst r) u0 := by
  show unglue _ _ (u0.dshift.dinst r) = _; rw [dshift_dinst]; rfl


theorem dshift_sk2 (X : Tm) : X.dshift.subst Tm.var (sk (.var 0) 2) = X.dshift.dshift := by
  rw [dshift_sk, subst_add2]

theorem app_sk2 (e u0 : Tm) : (app (fst e) u0.dshift).subst Tm.var (sk (.var 0) 2) =
    app (fst (e.dsubst (sk (.var 0) 2))) u0.dshift.dshift := by
  show app (fst (e.subst _ _)) (u0.dshift.subst _ _) = _; rw [dshift_sk2]; rfl

theorem isContr_fiber_inst (T A f a : Tm) :
    (isContr (fiber T.shift A.shift f.shift (var 0))).inst a = isContr (fiber T A f a) := by
  simp only [isContr, fiber, pathC]; scalc

theorem pathC_var0_inst (X c p : Tm) : (pathC X.shift c.shift (var 0)).inst p = pathC X c p := by
  simp only [pathC]; scalc

theorem tgFib_eq (A : Tm) (φ : I) (T e : Tm) (ψ : I) (u0 : Tm) : tgFib A φ T e ψ u0 =
    sigma (T.dinst .one) (pathC (A.dinst .one).shift (app (fst (e.dinst .one)).shift (var 0)) (tgA1' A φ e ψ u0).shift) :=
  rfl

theorem psys_dinst (δ ψ : I) (X Y : Tm) (r : I) :
    (split δ.shift (papp X.dshift (.var 0)) ψ.shift (papp Y.dshift (.var 0))).dinst r =
      split δ (papp X r) ψ (papp Y r) := by
  have h2 : ∀ x : I, x.shift.subst (I.inst0 r) = x := fun x => by
    simp only [I.shift, I.ren, I_subst_subst]; exact I_subst_var x
  show split (δ.shift.subst _) (papp (X.dshift.dinst r) _) (ψ.shift.subst _) (papp (Y.dshift.dinst r) _) = _
  rw [h2, h2, dshift_dinst, dshift_dinst]; rfl

theorem tgExt_eq (A : Tm) (φ : I) (T e : Tm) (ψ : I) (u0 : Tm) (δ : I) : tgExt A φ T e ψ u0 δ =
    hcomp (tgFib A φ T e ψ u0) (.or δ ψ) (split δ.shift (papp (tgPd A φ T e ψ u0).dshift (.var 0)) ψ.shift
      (papp (tgPpsi A φ e ψ u0).dshift (.var 0))) (fst (tgC A φ e ψ u0)) := rfl

theorem asys_dinst (φ1 ψ : I) (X Y : Tm) (r : I) :
    (split φ1.shift (papp X.dshift (.neg (.var 0))) ψ.shift Y.dshift).dinst r =
      split φ1 (papp X (.neg r)) ψ Y := by
  have h2 : ∀ x : I, x.shift.subst (I.inst0 r) = x := fun x => by
    simp only [I.shift, I.ren, I_subst_subst]; exact I_subst_var x
  show split (φ1.shift.subst _) (papp (X.dshift.dinst r) _) (ψ.shift.subst _) (Y.dshift.dinst r) = _
  rw [h2, h2, dshift_dinst, dshift_dinst]; rfl

theorem tgA1_eq (A : Tm) (φ : I) (T e : Tm) (ψ : I) (u0 : Tm) (δ : I) : tgA1 A φ T e ψ u0 δ =
    hcomp (A.dinst .one) (.or (φ.subst (I.inst0 .one)) ψ)
      (split (φ.subst (I.inst0 .one)).shift (papp (snd (tgExt A φ T e ψ u0 δ)).dshift (.neg (.var 0)))
        ψ.shift (tgA1' A φ e ψ u0).dshift) (tgA1' A φ e ψ u0) := rfl

/-- The cofibration of the composition in `ω`: `ψ ∨ j = 0 ∨ j = 1`. -/
abbrev tgChi (ψ : I) : I := .or ψ.shift (.or (.neg (.var 0)) (.var 0))

/-! ## The premises -/

structure TG (S : Sig) (Ψ : Nat) (Φ : I) (Γ : Ctx) (A : Tm) (φ : I) (T e : Tm) (ψ : I) (u0 : Tm) (δ : I)
    (l : Nat) : Prop where
  hS : SigClosed S
  hA : HasTy0 S (Ψ + 1) Φ.shift Γ.dshift A (univ l)
  hφ : φ.Scoped (Ψ + 1)
  hT : HasTy0 S (Ψ + 1) (cof Φ.shift φ) Γ.dshift T (univ l)
  he : HasTy0 S (Ψ + 1) (cof Φ.shift φ) Γ.dshift e (equiv T A)
  hψ : ψ.Scoped Ψ
  hδ : δ.Scoped Ψ
  hδφ : I.Entails δ φ.forall0
  hconst : EqTm0 S (Ψ + 1) (cof Φ ψ).shift Γ.dshift (glue A φ T e) ((glue A φ T e).dinst .zero).dshift (univ l)
  hu0 : HasTy0 S Ψ Φ Γ u0 ((glue A φ T e).dinst .zero)

namespace TG

variable {Ψ : Nat} {Φ : I} {Γ : Ctx} {A : Tm} {φ : I} {T e : Tm} {ψ : I} {u0 : Tm} {δ : I} {l : Nat}
  (H : TG S Ψ Φ Γ A φ T e ψ u0 δ l)
include H

theorem hw : Wf0 S Ψ Φ Γ := wf_of_ty H.hu0
theorem hs : Φ.Scoped Ψ := scoped_of_ty H.hu0

theorem hφr {r : I} (hr : r.Scoped Ψ) : (φ.subst (I.inst0 r)).Scoped Ψ :=
  scoped_subst H.hφ (fun i hi => by
    rcases i with _ | i
    · exact hr
    · exact show i < Ψ by omega)

theorem hG : HasTy0 S (Ψ + 1) Φ.shift Γ.dshift (glue A φ T e) (univ l) := HasTy0.glue H.hA H.hφ H.hT H.he

theorem hAr {r : I} (hr : r.Scoped Ψ) : HasTy0 S Ψ Φ Γ (A.dinst r) (univ l) := HasTy0.dsubst H.hS H.hA hr

theorem hGr {r : I} (hr : r.Scoped Ψ) :
    HasTy0 S Ψ Φ Γ (glue (A.dinst r) (φ.subst (I.inst0 r)) (T.dinst r) (e.dinst r)) (univ l) :=
  HasTy0.dsubst H.hS H.hG hr

theorem hTr {r : I} (hr : r.Scoped Ψ) {X : I} (hXs : X.Scoped Ψ) (hXΦ : I.Entails X Φ)
    (hXφ : I.Entails X (φ.subst (I.inst0 r))) : HasTy0 S Ψ X Γ (T.dinst r) (univ l) :=
  HasTy0.cof_inst H.hS H.hT H.hw hr hXs hXΦ hXφ

theorem her {r : I} (hr : r.Scoped Ψ) {X : I} (hXs : X.Scoped Ψ) (hXΦ : I.Entails X Φ)
    (hXφ : I.Entails X (φ.subst (I.inst0 r))) : HasTy0 S Ψ X Γ (e.dinst r) (equiv (T.dinst r) (A.dinst r)) := by
  have := HasTy0.cof_inst H.hS H.he H.hw hr hXs hXΦ hXφ
  rwa [equiv_dinst] at this

/-- `a0 = unglue u0 : A(0)` -/
theorem ha0 : HasTy0 S Ψ Φ Γ (tgA0 φ e u0) (A.dinst .zero) :=
  HasTy0.unglue (H.hGr (r := .zero) trivial) (H.hAr (r := .zero) trivial)
    (H.her (r := .zero) trivial ⟨H.hs, H.hφr (r := .zero) trivial⟩ (ent_and_left _ _) (ent_and_right _ _)) H.hu0

theorem hXψs : (cof Φ ψ).shift.Scoped (Ψ + 1) := scoped_shift ⟨H.hs, H.hψ⟩

/-- On `ψ`, `u0` lies in the line. -/
theorem hu0line : HasTy0 S (Ψ + 1) (cof Φ ψ).shift Γ.dshift u0.dshift (glue A φ T e) :=
  HasTy0.conv (HasTy0.restrict H.hXψs (ent_shift (ent_and_left _ _)) (HasTy0.dwk H.hS H.hu0))
    (EqTm0.symm H.hconst)

/-- The tube `i ↦ unglue u0 : A(i)` on `ψ`. -/
theorem htube : HasTy0 S (Ψ + 1) (cof Φ ψ).shift Γ.dshift (tgTube φ e u0) A := by
  have hXΦ : I.Entails (cof Φ ψ).shift Φ.shift := ent_shift (ent_and_left _ _)
  exact HasTy0.unglue (HasTy0.restrict H.hXψs hXΦ H.hG) (HasTy0.restrict H.hXψs hXΦ H.hA)
    (HasTy0.restrict ⟨H.hXψs, H.hφ⟩ (ent_and_mono hXΦ (ent_refl _)) H.he) H.hu0line

theorem htube_side : EqTm0 S Ψ (cof Φ ψ) Γ ((tgTube φ e u0).dinst .zero) (tgA0 φ e u0) (A.dinst .zero) := by
  rw [tgTube_dinst]; exact EqTm0.refl (HasTy0.restrict ⟨H.hs, H.hψ⟩ (ent_and_left _ _) H.ha0)

/-- `a1' = comp A [ψ ↦ tube] a0 : A(1)` -/
theorem ha1' : HasTy0 S Ψ Φ Γ (tgA1' A φ e ψ u0) (A.dinst .one) :=
  comp_typed H.hS H.hA H.hψ H.htube H.ha0 H.htube_side

/-! ### On `δ` (`∀i. φ`) the line is `T` -/

theorem hZs : (cof Φ δ).Scoped Ψ := ⟨H.hs, H.hδ⟩
theorem hZΦ : I.Entails (cof Φ δ) Φ := ent_and_left _ _
theorem hZφr (r : I) : I.Entails (cof Φ δ) (φ.subst (I.inst0 r)) :=
  ent_trans (ent_and_right _ _) (ent_forall_inst H.hδφ r)
theorem hZφ : I.Entails (cof Φ δ).shift φ :=
  ent_trans (ent_shift (ent_and_right Φ δ)) (ent_forall_shift H.hδφ)
theorem hZs1 : (cof Φ δ).shift.Scoped (Ψ + 1) := scoped_shift H.hZs

theorem hGT : EqTm0 S (Ψ + 1) (cof Φ δ).shift Γ.dshift (glue A φ T e) T (univ l) :=
  EqTm0.glueFace H.hZφ (HasTy0.restrict H.hZs1 (ent_shift H.hZΦ) H.hG)

theorem hGTr {r : I} (hr : r.Scoped Ψ) :
    EqTm0 S Ψ (cof Φ δ) Γ ((glue A φ T e).dinst r) (T.dinst r) (univ l) :=
  EqTm0.glueFace (H.hZφr r) (HasTy0.restrict H.hZs H.hZΦ (H.hGr hr))

theorem hTZ : HasTy0 S (Ψ + 1) (cof Φ δ).shift Γ.dshift T (univ l) :=
  HasTy0.cof_restrict H.hT H.hZs1 (ent_shift H.hZΦ) H.hZφ

theorem heZ : HasTy0 S (Ψ + 1) (cof Φ δ).shift Γ.dshift e (equiv T A) :=
  HasTy0.cof_restrict H.he H.hZs1 (ent_shift H.hZΦ) H.hZφ

theorem hZψs : (cof (cof Φ δ) ψ).Scoped Ψ := ⟨H.hZs, H.hψ⟩
theorem hZψs1 : (cof (cof Φ δ) ψ).shift.Scoped (Ψ + 1) := scoped_shift H.hZψs
theorem hZψΦψ : I.Entails (cof (cof Φ δ) ψ) (cof Φ ψ) := ent_and_mono H.hZΦ (ent_refl _)
theorem hZψZ : I.Entails (cof (cof Φ δ) ψ) (cof Φ δ) := ent_and_left _ _

/-- On `δ ∧ ψ`, `T` is constant. -/
theorem hconstT : EqTm0 S (Ψ + 1) (cof (cof Φ δ) ψ).shift Γ.dshift T (T.dinst .zero).dshift (univ l) := by
  have e1 := EqTm0.restrict H.hZψs1 (ent_shift H.hZψZ) H.hGT
  have e2 := EqTm0.restrict H.hZψs1 (ent_shift H.hZψΦψ) H.hconst
  have e3 := EqTm0.restrict H.hZψs1 (ent_shift H.hZψZ) (EqTm0.dwk H.hS (H.hGTr (r := .zero) trivial))
  exact EqTm0.trans (EqTm0.symm e1) (EqTm0.trans e2 e3)

theorem hu0T : HasTy0 S Ψ (cof Φ δ) Γ u0 (T.dinst .zero) :=
  HasTy0.conv (HasTy0.restrict H.hZs H.hZΦ H.hu0) (H.hGTr (r := .zero) trivial)

/-- `t1' = transp T ψ u0 : T(1)` on `δ` -/
theorem ht1 : HasTy0 S Ψ (cof Φ δ) Γ (tgT1 T ψ u0) (T.dinst .one) :=
  HasTy0.transp H.hTZ H.hψ H.hconstT H.hu0T

/-! ### The path `ω` on `δ` -/


theorem hδ2 : I.Entails δ.shift.shift (φ.subst (sk (.var 0) 2)) := by
  have := ent_forall_sk H.hδφ (.var 0) 2; rwa [I_add2] at this

theorem heIns {X : I} (hXs : X.Scoped (Ψ + 1 + 1)) (hX : I.Entails X (cof Φ δ).shift.shift) :
    HasTy0 S (Ψ + 1 + 1) X Γ.dshift.dshift (e.dsubst (sk (.var 0) 2))
      (equiv (T.dsubst (sk (.var 0) 2)) (A.dsubst (sk (.var 0) 2))) := by
  have := HasTy0.cof_ins H.hS H.he H.hw hXs (ent_trans hX (ent_shift (ent_shift (ent_and_left Φ δ))))
    (ent_trans hX (ent_trans (ent_shift (ent_shift (ent_and_right Φ δ))) H.hδ2))
  rwa [equiv_subst] at this

theorem hCIns {X : I} (hXs : X.Scoped (Ψ + 1 + 1)) (hX : I.Entails X Φ.shift.shift) :
    HasTy0 S (Ψ + 1 + 1) X Γ.dshift.dshift (A.dsubst (sk (.var 0) 2)) (univ l) :=
  HasTy0.sk2 H.hS H.hA (r := .var 0) (show 0 < Ψ + 1 + 1 by omega) hXs hX

theorem hu0Ins {X : I} (hXs : X.Scoped (Ψ + 1 + 1)) (hX : I.Entails X (cof (cof Φ δ) ψ).shift.shift) :
    HasTy0 S (Ψ + 1 + 1) X Γ.dshift.dshift u0.dshift.dshift (T.dsubst (sk (.var 0) 2)) := by
  have e := EqTm0.sk2 H.hS H.hconstT (r := .var 0) (show 0 < Ψ + 1 + 1 by omega) hXs hX
  rw [dshift_sk2] at e
  have hu := HasTy0.restrict hXs (ent_trans hX (ent_shift (ent_shift H.hZψZ)))
    (HasTy0.dwk H.hS (HasTy0.dwk H.hS H.hu0T))
  exact HasTy0.conv hu (EqTm0.symm e)

theorem htfIns {X : I} (hXs : X.Scoped (Ψ + 1 + 1)) (hX : I.Entails X (cof Φ δ).shift.shift) :
    HasTy0 S (Ψ + 1 + 1) X Γ.dshift.dshift ((transpFill T ψ u0).dsubst (sk (.var 0) 2)) (T.dsubst (sk (.var 0) 2)) :=
  HasTy0.sk2 H.hS (transpFill_typed H.hS H.hTZ H.hψ H.hconstT H.hu0T).1 (r := .var 0)
    (show 0 < Ψ + 1 + 1 by omega) hXs hX

theorem hfillIns {X : I} (hXs : X.Scoped (Ψ + 1 + 1)) (hX : I.Entails X Φ.shift.shift) :
    HasTy0 S (Ψ + 1 + 1) X Γ.dshift.dshift ((fill A ψ (tgTube φ e u0) (tgA0 φ e u0)).dsubst (sk (.var 0) 2))
      (A.dsubst (sk (.var 0) 2)) :=
  HasTy0.sk2 H.hS (fill_typed H.hS H.hA H.hψ H.htube H.ha0 H.htube_side).1 (r := .var 0)
    (show 0 < Ψ + 1 + 1 by omega) hXs hX

theorem E1 {X : I} (hXs : X.Scoped (Ψ + 1 + 1)) (hX : I.Entails X (cof (cof Φ δ) ψ).shift.shift) :
    EqTm0 S (Ψ + 1 + 1) X Γ.dshift.dshift ((transpFill T ψ u0).dsubst (sk (.var 0) 2)) u0.dshift.dshift
      (T.dsubst (sk (.var 0) 2)) := by
  have := EqTm0.sk2 H.hS (transpFill_typed H.hS H.hTZ H.hψ H.hconstT H.hu0T).2.2.2 (r := .var 0)
    (show 0 < Ψ + 1 + 1 by omega) hXs hX
  rwa [dshift_sk2] at this

/-- On `δ ∧ ψ` the filler of `a1'` is `e.1 u0`. -/
theorem hfillψδ : EqTm0 S (Ψ + 1) (cof (cof Φ δ) ψ).shift Γ.dshift (fill A ψ (tgTube φ e u0) (tgA0 φ e u0))
    (app (fst e) u0.dshift) A := by
  have e1 := EqTm0.restrict H.hZψs1 (ent_shift H.hZψΦψ)
    (fill_typed H.hS H.hA H.hψ H.htube H.ha0 H.htube_side).2.2.2
  have e2 := EqTm0.unglueFace (ent_trans (ent_shift H.hZψZ) H.hZφ)
    (HasTy0.restrict H.hZψs1 (ent_shift H.hZψΦψ) H.hu0line)
    (HasTy0.restrict H.hZψs1 (ent_shift (ent_trans H.hZψZ H.hZΦ)) H.hA)
    (HasTy0.restrict H.hZψs1 (ent_shift H.hZψZ) H.heZ)
  exact EqTm0.trans e1 e2

theorem E2 {X : I} (hXs : X.Scoped (Ψ + 1 + 1)) (hX : I.Entails X (cof (cof Φ δ) ψ).shift.shift) :
    EqTm0 S (Ψ + 1 + 1) X Γ.dshift.dshift ((fill A ψ (tgTube φ e u0) (tgA0 φ e u0)).dsubst (sk (.var 0) 2))
      (app (fst (e.dsubst (sk (.var 0) 2))) u0.dshift.dshift) (A.dsubst (sk (.var 0) 2)) := by
  have := EqTm0.sk2 H.hS H.hfillψδ (r := .var 0) (show 0 < Ψ + 1 + 1 by omega) hXs hX
  rwa [app_sk2] at this

/-- The system of `ω`. -/
theorem hsys : HasTy0 S (Ψ + 1 + 1) (cof (cof Φ δ).shift (tgChi ψ)).shift Γ.dshift.dshift
    (tgSys A φ T e ψ u0) (A.dsubst (sk (.var 0) 2)) := by
  have hv0 : (I.var 0).Scoped (Ψ + 1) := show 0 < Ψ + 1 by omega
  have hv1 : (I.var 1).Scoped (Ψ + 1 + 1) := show 1 < Ψ + 1 + 1 by omega
  have hRs : (cof (cof Φ δ).shift (tgChi ψ)).shift.Scoped (Ψ + 1 + 1) :=
    scoped_shift ⟨H.hZs1, ⟨scoped_shift H.hψ, ⟨hv0, hv0⟩⟩⟩
  have hRZ : I.Entails (cof (cof Φ δ).shift (tgChi ψ)).shift (cof Φ δ).shift.shift := ent_shift (ent_and_left _ _)
  have hRχ : I.Entails (cof (cof Φ δ).shift (tgChi ψ)).shift (.or ψ.shift.shift (.or (.neg (.var 1)) (.var 1))) :=
    ent_shift (ent_and_right (cof Φ δ).shift (tgChi ψ))
  generalize (cof (cof Φ δ).shift (tgChi ψ)).shift = R at hRs hRZ hRχ ⊢
  have hZΦ2 : I.Entails (cof Φ δ).shift.shift Φ.shift.shift := ent_shift (ent_shift (ent_and_left Φ δ))
  have hZψ2 : ∀ {X : I}, I.Entails X (cof Φ δ).shift.shift → I.Entails X ψ.shift.shift →
      I.Entails X (cof (cof Φ δ) ψ).shift.shift := fun h1 h2 =>
    show I.Entails _ (.and _ _) from ent_and_intro h1 h2
  have hψ2 : ψ.shift.shift.Scoped (Ψ + 1 + 1) := scoped_shift (scoped_shift H.hψ)
  -- the branch `ψ`
  have hR1s : (cof R ψ.shift.shift).Scoped (Ψ + 1 + 1) := ⟨hRs, hψ2⟩
  have hR1Z : I.Entails (cof R ψ.shift.shift) (cof Φ δ).shift.shift := ent_trans (ent_and_left R _) hRZ
  have hR1W := hZψ2 hR1Z (ent_and_right R _)
  have b1 := app_fst_equiv (H.heIns hR1s hR1Z) (H.hu0Ins hR1s hR1W)
  -- the inner system
  let j2 : I := .or (.neg (.var 1)) (.var 1)
  have hR2s : (cof R j2).Scoped (Ψ + 1 + 1) := ⟨hRs, ⟨hv1, hv1⟩⟩
  have hR2Z : I.Entails (cof R j2) (cof Φ δ).shift.shift := ent_trans (ent_and_left R j2) hRZ
  have hR21s : (cof (cof R j2) (.neg (.var 1))).Scoped (Ψ + 1 + 1) := ⟨hR2s, hv1⟩
  have hR22s : (cof (cof R j2) (.var 1)).Scoped (Ψ + 1 + 1) := ⟨hR2s, hv1⟩
  have hR21Z : I.Entails (cof (cof R j2) (.neg (.var 1))) (cof Φ δ).shift.shift := ent_trans (ent_and_left _ (.neg (.var 1))) hR2Z
  have hR22Z : I.Entails (cof (cof R j2) (.var 1)) (cof Φ δ).shift.shift := ent_trans (ent_and_left _ (.var 1)) hR2Z
  have b2 := app_fst_equiv (H.heIns hR21s hR21Z) (H.htfIns hR21s hR21Z)
  have b3 := H.hfillIns hR22s (ent_trans hR22Z hZΦ2)
  have hinner : HasTy0 S (Ψ + 1 + 1) (cof R j2) Γ.dshift.dshift
      (split (.neg (.var 1)) (app (fst (e.dsubst (sk (.var 0) 2))) ((transpFill T ψ u0).dsubst (sk (.var 0) 2)))
        (.var 1) ((fill A ψ (tgTube φ e u0) (tgA0 φ e u0)).dsubst (sk (.var 0) 2))) (A.dsubst (sk (.var 0) 2)) :=
    HasTy0.split hv1 hv1 (ent_and_right R j2) (H.hCIns hR2s (ent_trans hR2Z hZΦ2)) b2 b3
      (EqTm0.absurd (ent_contra (cof R j2) 1)
        (HasTy0.restrict ⟨hR21s, hv1⟩ (ent_and_left _ (.var 1)) b2)
        (HasTy0.restrict ⟨hR21s, hv1⟩ (ent_and_mono (ent_and_left (cof R j2) (.neg (.var 1))) (ent_refl (.var 1))) b3))
  -- agreement
  have hYs : (cof (cof R ψ.shift.shift) j2).Scoped (Ψ + 1 + 1) := ⟨hR1s, ⟨hv1, hv1⟩⟩
  have hYR2 : I.Entails (cof (cof R ψ.shift.shift) j2) (cof R j2) :=
    ent_and_mono (ent_and_left R ψ.shift.shift) (ent_refl j2)
  have hYW : I.Entails (cof (cof R ψ.shift.shift) j2) (cof (cof Φ δ) ψ).shift.shift :=
    ent_trans (ent_and_left _ j2) hR1W
  have hYZ : I.Entails (cof (cof R ψ.shift.shift) j2) (cof Φ δ).shift.shift := ent_trans hYR2 hR2Z
  have hover := EqTm0.local (φ := .neg (.var 1)) (ψ := .var 1) hv1 hv1 (ent_and_right _ j2)
    (HasTy0.restrict hYs (ent_and_left _ j2) b1) (HasTy0.restrict hYs hYR2 hinner)
    (by
      have hs1 : (cof (cof (cof R ψ.shift.shift) j2) (.neg (.var 1))).Scoped (Ψ + 1 + 1) := ⟨hYs, hv1⟩
      have hl := ent_and_left (cof (cof R ψ.shift.shift) j2) (.neg (.var 1))
      have s1 := EqTm0.splitL (ent_and_right _ (.neg (.var 1))) (HasTy0.restrict hs1 (ent_trans hl hYR2) hinner)
      have c1 := app_fst_congr (H.heIns hs1 (ent_trans hl hYZ)) (EqTm0.symm (H.E1 hs1 (ent_trans hl hYW)))
      exact EqTm0.trans c1 (EqTm0.symm s1))
    (by
      have hs1 : (cof (cof (cof R ψ.shift.shift) j2) (.var 1)).Scoped (Ψ + 1 + 1) := ⟨hYs, hv1⟩
      have hl := ent_and_left (cof (cof R ψ.shift.shift) j2) (.var 1)
      have s2 := EqTm0.splitR (ent_and_right _ (.var 1)) (HasTy0.restrict hs1 (ent_trans hl hYR2) hinner)
      exact EqTm0.trans (EqTm0.symm (H.E2 hs1 (ent_trans hl hYW))) (EqTm0.symm s2))
  exact HasTy0.split hψ2 ⟨hv1, hv1⟩ hRχ (H.hCIns hRs (ent_trans hRZ hZΦ2)) b1 hinner hover

theorem he0Z (r : I) (hr : r.Scoped Ψ) : HasTy0 S Ψ (cof Φ δ) Γ (e.dinst r) (equiv (T.dinst r) (A.dinst r)) :=
  H.her hr H.hZs H.hZΦ (H.hZφr r)

theorem hbaseω : HasTy0 S (Ψ + 1) (cof Φ δ).shift Γ.dshift (app (fst (e.dinst .zero).dshift) u0.dshift)
    ((A.dsubst (sk (.var 0) 2)).dinst .zero) := by
  rw [L_C0]; exact HasTy0.dwk H.hS (app_fst_equiv (H.he0Z .zero trivial) H.hu0T)

/-- On `δ`, `fill(0) ≡ e(0).1 u0`. -/
theorem hfill0 : EqTm0 S Ψ (cof Φ δ) Γ ((fill A ψ (tgTube φ e u0) (tgA0 φ e u0)).dinst .zero)
    (app (fst (e.dinst .zero)) u0) (A.dinst .zero) := by
  have e1 := EqTm0.restrict H.hZs H.hZΦ (fill_typed H.hS H.hA H.hψ H.htube H.ha0 H.htube_side).2.1
  have e2 := EqTm0.unglueFace (H.hZφr .zero) (HasTy0.restrict H.hZs H.hZΦ H.hu0)
    (HasTy0.restrict H.hZs H.hZΦ (H.hAr (r := .zero) trivial)) (H.he0Z .zero trivial)
  exact EqTm0.trans e1 e2

theorem hsideω : EqTm0 S (Ψ + 1) (cof (cof Φ δ).shift (tgChi ψ)) Γ.dshift ((tgSys A φ T e ψ u0).dinst .zero)
    (app (fst (e.dinst .zero).dshift) u0.dshift) ((A.dsubst (sk (.var 0) 2)).dinst .zero) := by
  have hv0 : (I.var 0).Scoped (Ψ + 1) := show 0 < Ψ + 1 by omega
  have hQs : (cof (cof Φ δ).shift (tgChi ψ)).Scoped (Ψ + 1) := ⟨H.hZs1, ⟨scoped_shift H.hψ, ⟨hv0, hv0⟩⟩⟩
  have hQZ : I.Entails (cof (cof Φ δ).shift (tgChi ψ)) (cof Φ δ).shift := ent_and_left _ _
  have hQχ : I.Entails (cof (cof Φ δ).shift (tgChi ψ)) (.or ψ.shift (.or (.neg (.var 0)) (.var 0))) :=
    ent_and_right _ _
  have hs0 := HasTy0.dsubst H.hS H.hsys (r := .zero) trivial
  have hb := HasTy0.restrict hQs hQZ H.hbaseω
  rw [L_C0] at hs0 hb ⊢
  have tf0 := (transpFill_typed H.hS H.hTZ H.hψ H.hconstT H.hu0T).2.1
  generalize (cof (cof Φ δ).shift (tgChi ψ)) = Q at hQs hQZ hQχ hs0 hb ⊢
  simp only [tgSys] at hs0 ⊢
  rw [sys_d _ _ _ _ _ _ (.inl rfl)] at hs0 ⊢
  obtain ⟨A', ⟨_, _, _, _, hin⟩, ch⟩ := gen_split hs0 rfl
  have hQ2s : (cof Q (.or (.neg (.var 0)) (.var 0))).Scoped (Ψ + 1) := ⟨hQs, ⟨hv0, hv0⟩⟩
  have hin' := (ch.restrict hQ2s (ent_and_left _ _)).transport hin
  refine EqTm0.local (φ := ψ.shift) (ψ := .or (.neg (.var 0)) (.var 0)) (scoped_shift H.hψ) ⟨hv0, hv0⟩ hQχ hs0 hb ?_ ?_
  · exact EqTm0.splitL (ent_and_right _ _) (HasTy0.restrict ⟨hQs, scoped_shift H.hψ⟩ (ent_and_left _ _) hs0)
  · refine EqTm0.trans (EqTm0.splitR (ent_and_right _ _) (HasTy0.restrict hQ2s (ent_and_left _ _) hs0)) ?_
    have hQ2Z : I.Entails (cof Q (.or (.neg (.var 0)) (.var 0))) (cof Φ δ).shift := ent_trans (ent_and_left _ _) hQZ
    refine EqTm0.local (φ := .neg (.var 0)) (ψ := .var 0) hv0 hv0 (ent_and_right _ _) hin'
      (HasTy0.restrict hQ2s (ent_and_left _ _) hb) ?_ ?_
    · have hs1 : (cof (cof Q (.or (.neg (.var 0)) (.var 0))) (.neg (.var 0))).Scoped (Ψ + 1) := ⟨hQ2s, hv0⟩
      refine EqTm0.trans (EqTm0.splitL (ent_and_right _ _) (HasTy0.restrict hs1 (ent_and_left _ _) hin')) ?_
      exact EqTm0.restrict hs1 (ent_trans (ent_and_left _ _) hQ2Z)
        (EqTm0.dwk H.hS (app_fst_congr (H.he0Z .zero trivial) tf0))
    · have hs1 : (cof (cof Q (.or (.neg (.var 0)) (.var 0))) (.var 0)).Scoped (Ψ + 1) := ⟨hQ2s, hv0⟩
      refine EqTm0.trans (EqTm0.splitR (ent_and_right _ _) (HasTy0.restrict hs1 (ent_and_left _ _) hin')) ?_
      exact EqTm0.restrict hs1 (ent_trans (ent_and_left _ _) hQ2Z) (EqTm0.dwk H.hS H.hfill0)

theorem hbody : HasTy0 S (Ψ + 1) (cof Φ δ).shift Γ.dshift (tgBody A φ T e ψ u0) (A.dinst .one).dshift := by
  have hv0 : (I.var 0).Scoped (Ψ + 1) := show 0 < Ψ + 1 by omega
  have := comp_typed H.hS (H.hCIns (scoped_shift H.hZs1) (ent_shift (ent_shift (ent_and_left Φ δ))))
    (show (tgChi ψ).Scoped (Ψ + 1) from ⟨scoped_shift H.hψ, ⟨hv0, hv0⟩⟩) H.hsys H.hbaseω H.hsideω
  rwa [L_C1] at this

theorem hA1Z : HasTy0 S Ψ (cof Φ δ) Γ (A.dinst .one) (univ l) :=
  HasTy0.restrict H.hZs H.hZΦ (H.hAr (r := .one) trivial)

/-- The ends of `ω`. -/
theorem hωend (d : Bool) : EqTm0 S Ψ (cof Φ δ) Γ ((tgBody A φ T e ψ u0).dinst (I.ofDir d))
    (split (.neg (I.ofDir d)) (app (fst (e.dinst .one)) ((transpFill T ψ u0).dinst .one)) (I.ofDir d)
      ((fill A ψ (tgTube φ e u0) (tgA0 φ e u0)).dinst .one)) (A.dinst .one) ∧
    HasTy0 S Ψ (cof Φ δ) Γ (split (.neg (I.ofDir d)) (app (fst (e.dinst .one)) ((transpFill T ψ u0).dinst .one))
      (I.ofDir d) ((fill A ψ (tgTube φ e u0) (tgA0 φ e u0)).dinst .one)) (A.dinst .one) := by
  have hdd : (I.ofDir d).Scoped Ψ := by cases d <;> trivial
  have hor : I.Entails (cof Φ δ) (.or (.neg (I.ofDir d)) (I.ofDir d)) := by
    cases d
    · exact ent_negzero_or _
    · exact ent_one_or _
  have hb0 := HasTy0.dsubst H.hS H.hbody hdd
  rw [dshift_dinst, tgBody_dinst] at hb0
  have e1 := comp_face H.hS hb0 (ent_trans hor (ent_or_right _ _))
  have hE := HasTy0.isub H.hS (τ := endS d) H.hsys (endS_scoped Ψ d)
    (ent_and_intro (ent_shift2_endS (cof Φ δ) d) (ent_trans hor (ent_or_right _ _)))
    (by rw [ctxI_endS]; exact H.hw.restrict H.hZs H.hZΦ)
  rw [ctxI_endS, L_CE] at hE
  have hsE : (tgSys A φ T e ψ u0).subst Tm.var (endS d) = split ψ (app (fst (e.dinst .one)) u0)
      (.or (.neg (I.ofDir d)) (I.ofDir d)) (split (.neg (I.ofDir d)) (app (fst (e.dinst .one))
        ((transpFill T ψ u0).dinst .one)) (I.ofDir d) ((fill A ψ (tgTube φ e u0) (tgA0 φ e u0)).dinst .one)) :=
    sys_end _ _ _ _ _ d
  have hu : ((tgSys A φ T e ψ u0).subst Tm.var (I.up (I.inst0 (I.ofDir d)))).dinst .one =
      (tgSys A φ T e ψ u0).subst Tm.var (endS d) := by cases d <;> ssub
  rw [hu, hsE] at e1
  rw [hsE] at hE
  obtain ⟨A', ⟨_, _, _, _, hin⟩, ch⟩ := gen_split hE rfl
  have hin' := (ch.restrict (show (cof (cof Φ δ) (.or (.neg (I.ofDir d)) (I.ofDir d))).Scoped Ψ from
    ⟨H.hZs, ⟨hdd, hdd⟩⟩) (ent_and_left _ _)).transport hin
  have hin'' := HasTy0.restrict H.hZs (ent_and_intro (ent_refl _) hor) hin'
  rw [tgBody_dinst]
  exact ⟨EqTm0.trans e1 (EqTm0.splitR hor hE), hin''⟩

theorem hω0 : EqTm0 S Ψ (cof Φ δ) Γ ((tgBody A φ T e ψ u0).dinst .zero)
    (app (fst (e.dinst .one)) (tgT1 T ψ u0)) (A.dinst .one) := by
  obtain ⟨e1, hin⟩ := H.hωend false
  have e2 := EqTm0.splitL (ent_negzero _) hin
  have e3 := app_fst_congr (H.he0Z .one trivial) (transpFill_typed H.hS H.hTZ H.hψ H.hconstT H.hu0T).2.2.1
  exact EqTm0.trans e1 (EqTm0.trans e2 e3)

theorem hω1 : EqTm0 S Ψ (cof Φ δ) Γ ((tgBody A φ T e ψ u0).dinst .one) (tgA1' A φ e ψ u0) (A.dinst .one) := by
  obtain ⟨e1, hin⟩ := H.hωend true
  have e2 := EqTm0.splitR (ent_one _) hin
  have e3 := EqTm0.restrict H.hZs H.hZΦ (fill_typed H.hS H.hA H.hψ H.htube H.ha0 H.htube_side).2.2.1
  exact EqTm0.trans e1 (EqTm0.trans e2 e3)

theorem ha1'Z : HasTy0 S Ψ (cof Φ δ) Γ (tgA1' A φ e ψ u0) (A.dinst .one) := HasTy0.restrict H.hZs H.hZΦ H.ha1'

/-- `ω : Path A(1) (e(1).1 t1') a1'` -/
theorem hω : HasTy0 S Ψ (cof Φ δ) Γ (tgOmega A φ T e ψ u0)
    (pathC (A.dinst .one) (app (fst (e.dinst .one)) (tgT1 T ψ u0)) (tgA1' A φ e ψ u0)) :=
  HasTy0.plam (pathC_typed H.hS H.hA1Z (app_fst_equiv (H.he0Z .one trivial) H.ht1) H.ha1'Z) H.hbody
    (by rw [dshift_dinst]; exact H.hω0) (by rw [dshift_dinst]; exact H.hω1)

/-! ### The fibre -/

theorem hWs : (cof Φ (φ.subst (I.inst0 .one))).Scoped Ψ := ⟨H.hs, H.hφr (r := .one) trivial⟩

theorem he1 : HasTy0 S Ψ (cof Φ (φ.subst (I.inst0 .one))) Γ (e.dinst .one) (equiv (T.dinst .one) (A.dinst .one)) :=
  H.her (r := .one) trivial H.hWs (ent_and_left _ _) (ent_and_right _ _)

theorem hfe1 : HasTy0 S Ψ (cof Φ (φ.subst (I.inst0 .one))) Γ (fst (e.dinst .one)) (arrow (T.dinst .one) (A.dinst .one)) :=
  HasTy0.fst H.he1

theorem hfib : HasTy0 S Ψ (cof Φ (φ.subst (I.inst0 .one))) Γ (tgFib A φ T e ψ u0) (univ l) :=
  fiber_typed H.hS (H.hTr (r := .one) trivial H.hWs (ent_and_left _ _) (ent_and_right _ _))
    (HasTy0.restrict H.hWs (ent_and_left _ _) (H.hAr (r := .one) trivial)) H.hfe1
    (HasTy0.restrict H.hWs (ent_and_left _ _) H.ha1')

/-- `c = e(1).2 a1' : isContr (fiber e(1).1 a1')` -/
theorem hc : HasTy0 S Ψ (cof Φ (φ.subst (I.inst0 .one))) Γ (tgC A φ e ψ u0) (isContr (tgFib A φ T e ψ u0)) := by
  have h1 := HasTy0.snd H.he1
  rw [isEquiv_inst, isEquiv_eq] at h1
  have := HasTy0.app h1 (HasTy0.restrict H.hWs (ent_and_left _ _) H.ha1')
  rwa [isContr_fiber_inst] at this

theorem hfc : HasTy0 S Ψ (cof Φ (φ.subst (I.inst0 .one))) Γ (fst (tgC A φ e ψ u0)) (tgFib A φ T e ψ u0) :=
  HasTy0.fst H.hc

/-- Contractibility: `c.2 p : Path fib c.1 p`. -/
theorem hcp {X : I} (hXs : X.Scoped Ψ) (hX : I.Entails X (cof Φ (φ.subst (I.inst0 .one)))) {p : Tm}
    (hp : HasTy0 S Ψ X Γ p (tgFib A φ T e ψ u0)) :
    HasTy0 S Ψ X Γ (app (snd (tgC A φ e ψ u0)) p) (pathC (tgFib A φ T e ψ u0) (fst (tgC A φ e ψ u0)) p) := by
  have h1 := HasTy0.snd (HasTy0.restrict hXs hX H.hc)
  rw [K_inst] at h1
  have := HasTy0.app h1 hp
  rwa [pathC_var0_inst] at this

theorem hcpEq {X : I} (hXs : X.Scoped Ψ) (hX : I.Entails X (cof Φ (φ.subst (I.inst0 .one)))) {p p' : Tm}
    (hp : EqTm0 S Ψ X Γ p p' (tgFib A φ T e ψ u0)) :
    EqTm0 S Ψ X Γ (app (snd (tgC A φ e ψ u0)) p) (app (snd (tgC A φ e ψ u0)) p')
      (pathC (tgFib A φ T e ψ u0) (fst (tgC A φ e ψ u0)) p) := by
  have h1 := HasTy0.snd (HasTy0.restrict hXs hX H.hc)
  rw [K_inst] at h1
  have := EqTm0.app (EqTm0.refl h1) hp
  rwa [pathC_var0_inst] at this

theorem hWδs : (cof (cof Φ (φ.subst (I.inst0 .one))) δ).Scoped Ψ := ⟨H.hWs, H.hδ⟩
theorem hWψs : (cof (cof Φ (φ.subst (I.inst0 .one))) ψ).Scoped Ψ := ⟨H.hWs, H.hψ⟩
theorem hWδZ : I.Entails (cof (cof Φ (φ.subst (I.inst0 .one))) δ) (cof Φ δ) :=
  ent_and_mono (ent_and_left _ _) (ent_refl _)

/-- The partial element of the fibre on `δ`: `(t1', ω)`. -/
theorem hpd : HasTy0 S Ψ (cof (cof Φ (φ.subst (I.inst0 .one))) δ) Γ
    (pair (tgT1 T ψ u0) (tgOmega A φ T e ψ u0)) (tgFib A φ T e ψ u0) := by
  have hf := HasTy0.restrict H.hWδs (ent_and_left _ _) H.hfib
  rw [tgFib_eq] at hf ⊢
  exact HasTy0.pair hf (HasTy0.restrict H.hWδs H.hWδZ H.ht1)
    (by rw [P_inst]; exact HasTy0.restrict H.hWδs H.hWδZ H.hω)

theorem hu0T1 : HasTy0 S Ψ (cof (cof Φ (φ.subst (I.inst0 .one))) ψ) Γ u0 (T.dinst .one) := by
  have hX : I.Entails (cof (cof Φ (φ.subst (I.inst0 .one))) ψ) (cof Φ ψ) := ent_and_mono (ent_and_left _ _) (ent_refl _)
  have hGψ := EqTm0.dsubst H.hS H.hconst (r := .one) trivial
  rw [dshift_dinst] at hGψ
  have hG1T1 := EqTm0.glueFace (ent_trans (ent_and_left _ _) (ent_and_right _ _))
    (HasTy0.restrict H.hWψs (ent_trans (ent_and_left _ _) (ent_and_left _ _)) (H.hGr (r := .one) trivial))
  exact HasTy0.conv (HasTy0.conv (HasTy0.restrict H.hWψs (ent_trans hX (ent_and_left _ _)) H.hu0)
    (EqTm0.symm (EqTm0.restrict H.hWψs hX hGψ))) hG1T1

theorem he1W {X : I} (hXs : X.Scoped Ψ) (hX : I.Entails X (cof Φ (φ.subst (I.inst0 .one)))) :
    HasTy0 S Ψ X Γ (e.dinst .one) (equiv (T.dinst .one) (A.dinst .one)) := HasTy0.restrict hXs hX H.he1

theorem hA1X {X : I} (hXs : X.Scoped Ψ) (hX : I.Entails X Φ) : HasTy0 S Ψ X Γ (A.dinst .one) (univ l) :=
  HasTy0.restrict hXs hX (H.hAr (r := .one) trivial)

/-- On `ψ`, `a1' ≡ e(1).1 u0`. -/
theorem ha1'eq : EqTm0 S Ψ (cof (cof Φ (φ.subst (I.inst0 .one))) ψ) Γ (tgA1' A φ e ψ u0)
    (app (fst (e.dinst .one)) u0) (A.dinst .one) := by
  have hX : I.Entails (cof (cof Φ (φ.subst (I.inst0 .one))) ψ) Φ := ent_trans (ent_and_left _ _) (ent_and_left _ _)
  have e1 := comp_face H.hS (HasTy0.restrict H.hWψs hX H.ha1') (ent_and_right _ _)
  rw [tgTube_dinst] at e1
  have hu0G1 : HasTy0 S Ψ (cof (cof Φ (φ.subst (I.inst0 .one))) ψ) Γ u0 ((glue A φ T e).dinst .one) := by
    have hGψ := EqTm0.dsubst H.hS H.hconst (r := .one) trivial
    rw [dshift_dinst] at hGψ
    exact HasTy0.conv (HasTy0.restrict H.hWψs hX H.hu0)
      (EqTm0.symm (EqTm0.restrict H.hWψs (ent_and_mono (ent_and_left _ _) (ent_refl _)) hGψ))
  have e2 := EqTm0.unglueFace (ent_trans (ent_and_left _ _) (ent_and_right _ _)) hu0G1
    (H.hA1X H.hWψs hX) (H.he1W H.hWψs (ent_and_left _ _))
  exact EqTm0.trans e1 e2

theorem hpl : HasTy0 S Ψ (cof (cof Φ (φ.subst (I.inst0 .one))) ψ) Γ (plam (tgA1' A φ e ψ u0).dshift)
    (pathC (A.dinst .one) (app (fst (e.dinst .one)) u0) (tgA1' A φ e ψ u0)) := by
  have hX : I.Entails (cof (cof Φ (φ.subst (I.inst0 .one))) ψ) Φ := ent_trans (ent_and_left _ _) (ent_and_left _ _)
  exact plam_const H.hS (H.hA1X H.hWψs hX)
    (app_fst_equiv (H.he1W H.hWψs (ent_and_left _ _)) H.hu0T1) (HasTy0.restrict H.hWψs hX H.ha1') H.ha1'eq

/-- The partial element of the fibre on `ψ`: `(u0, ⟨_⟩ a1')`. -/
theorem hpψ : HasTy0 S Ψ (cof (cof Φ (φ.subst (I.inst0 .one))) ψ) Γ
    (pair u0 (plam (tgA1' A φ e ψ u0).dshift)) (tgFib A φ T e ψ u0) := by
  have hf := HasTy0.restrict H.hWψs (ent_and_left _ _) H.hfib
  rw [tgFib_eq] at hf ⊢
  exact HasTy0.pair hf H.hu0T1 (by rw [P_inst]; exact H.hpl)

/-- On `δ ∧ ψ` the two partial elements agree. -/
theorem hpEq : EqTm0 S Ψ (cof (cof (cof Φ (φ.subst (I.inst0 .one))) δ) ψ) Γ
    (pair (tgT1 T ψ u0) (tgOmega A φ T e ψ u0)) (pair u0 (plam (tgA1' A φ e ψ u0).dshift)) (tgFib A φ T e ψ u0) := by
  have hv0 : (I.var 0).Scoped (Ψ + 1) := show 0 < Ψ + 1 by omega
  have hVs : (cof (cof (cof Φ (φ.subst (I.inst0 .one))) δ) ψ).Scoped Ψ := ⟨H.hWδs, H.hψ⟩
  have hVW : I.Entails (cof (cof (cof Φ (φ.subst (I.inst0 .one))) δ) ψ) (cof Φ (φ.subst (I.inst0 .one))) :=
    ent_trans (ent_and_left _ _) (ent_and_left _ _)
  have hVWψ : I.Entails (cof (cof (cof Φ (φ.subst (I.inst0 .one))) δ) ψ) (cof (cof Φ (φ.subst (I.inst0 .one))) ψ) :=
    ent_and_mono (ent_and_left _ _) (ent_refl _)
  have hVZ : I.Entails (cof (cof (cof Φ (φ.subst (I.inst0 .one))) δ) ψ) (cof Φ δ) :=
    ent_trans (ent_and_left _ _) H.hWδZ
  have hVΦ : I.Entails (cof (cof (cof Φ (φ.subst (I.inst0 .one))) δ) ψ) Φ := ent_trans hVW (ent_and_left _ _)
  have et := EqTm0.transpFace (ent_and_right _ _) (HasTy0.restrict hVs hVZ H.ht1)
  have he1V := H.he1W hVs hVW
  have hA1V := H.hA1X hVs hVΦ
  have ha1V := HasTy0.restrict hVs hVΦ H.ha1'
  have ea := EqTm0.trans (EqTm0.restrict hVs hVWψ H.ha1'eq) (app_fst_congr he1V (EqTm0.symm et))
  have hpl' := plam_const H.hS hA1V (app_fst_equiv he1V (HasTy0.restrict hVs hVZ H.ht1)) ha1V ea
  have hωV := HasTy0.restrict hVs hVZ H.hω
  -- the bodies
  have hVs1 := scoped_shift hVs
  have hbV := HasTy0.restrict hVs1 (ent_shift hVZ) H.hbody
  have hVχ : I.Entails (cof (cof (cof Φ (φ.subst (I.inst0 .one))) δ) ψ).shift (tgChi ψ) :=
    ent_trans (ent_shift (ent_and_right _ _)) (ent_or_left _ _)
  have e1 := comp_face H.hS hbV hVχ
  have hs1 := HasTy0.dsubst H.hS H.hsys (r := .one) trivial
  rw [L_C1] at hs1
  have hs1V := HasTy0.restrict hVs1 (ent_and_intro (ent_shift hVZ) hVχ) hs1
  simp only [tgSys] at e1 hs1V
  rw [sys_d _ _ _ _ _ _ (.inr rfl)] at e1 hs1V
  have e2 := EqTm0.splitL (ent_shift (ent_and_right _ _)) hs1V
  have e3 := EqTm0.dwk H.hS (EqTm0.symm (EqTm0.restrict hVs hVWψ H.ha1'eq))
  have eb : EqTm0 S (Ψ + 1) (cof (cof (cof Φ (φ.subst (I.inst0 .one))) δ) ψ).shift Γ.dshift
      (tgBody A φ T e ψ u0) (tgA1' A φ e ψ u0).dshift (A.dinst .one).dshift :=
    EqTm0.trans e1 (EqTm0.trans e2 e3)
  have eω := EqTm0.plam (pathC_typed H.hS hA1V (app_fst_equiv he1V (HasTy0.restrict hVs hVZ H.ht1)) ha1V)
    hωV hpl' eb
  have hf := HasTy0.restrict hVs (ent_trans (ent_and_left _ _) (ent_and_left _ _)) H.hfib
  rw [tgFib_eq] at hf ⊢
  exact EqTm0.pair hf et (by rw [P_inst]; exact eω)

/-! ### Extending the partial fibre element -/

theorem hPd : HasTy0 S Ψ (cof (cof Φ (φ.subst (I.inst0 .one))) δ) Γ (tgPd A φ T e ψ u0)
    (pathC (tgFib A φ T e ψ u0) (fst (tgC A φ e ψ u0)) (pair (tgT1 T ψ u0) (tgOmega A φ T e ψ u0))) :=
  H.hcp H.hWδs (ent_and_left _ _) H.hpd

theorem hPψ : HasTy0 S Ψ (cof (cof Φ (φ.subst (I.inst0 .one))) ψ) Γ (tgPpsi A φ e ψ u0)
    (pathC (tgFib A φ T e ψ u0) (fst (tgC A φ e ψ u0)) (pair u0 (plam (tgA1' A φ e ψ u0).dshift))) :=
  H.hcp H.hWψs (ent_and_left _ _) H.hpψ

theorem hPEq : EqTm0 S Ψ (cof (cof (cof Φ (φ.subst (I.inst0 .one))) δ) ψ) Γ (tgPd A φ T e ψ u0) (tgPpsi A φ e ψ u0)
    (pathC (tgFib A φ T e ψ u0) (fst (tgC A φ e ψ u0)) (pair (tgT1 T ψ u0) (tgOmega A φ T e ψ u0))) :=
  H.hcpEq (show (cof (cof (cof Φ (φ.subst (I.inst0 .one))) δ) ψ).Scoped Ψ from ⟨H.hWδs, H.hψ⟩)
    (ent_trans (ent_and_left _ _) (ent_and_left _ _)) H.hpEq

theorem hpsys : HasTy0 S (Ψ + 1) (cof (cof Φ (φ.subst (I.inst0 .one))) (.or δ ψ)).shift Γ.dshift
    (split δ.shift (papp (tgPd A φ T e ψ u0).dshift (.var 0)) ψ.shift (papp (tgPpsi A φ e ψ u0).dshift (.var 0)))
    (tgFib A φ T e ψ u0).dshift := by
  have hv0 : (I.var 0).Scoped (Ψ + 1) := show 0 < Ψ + 1 by omega
  have hΞs : (cof (cof Φ (φ.subst (I.inst0 .one))) (.or δ ψ)).shift.Scoped (Ψ + 1) :=
    scoped_shift ⟨H.hWs, ⟨H.hδ, H.hψ⟩⟩
  have hΞW : I.Entails (cof (cof Φ (φ.subst (I.inst0 .one))) (.or δ ψ)).shift (cof Φ (φ.subst (I.inst0 .one))).shift :=
    ent_shift (ent_and_left _ _)
  have hΞχ : I.Entails (cof (cof Φ (φ.subst (I.inst0 .one))) (.or δ ψ)).shift (.or δ.shift ψ.shift) :=
    ent_shift (ent_and_right _ (.or δ ψ))
  have hd := HasTy0.dwk H.hS H.hPd
  have hp := HasTy0.dwk H.hS H.hPψ
  have he := EqTm0.dwk H.hS H.hPEq
  rw [pathC_dshift] at hd hp he
  generalize (cof (cof Φ (φ.subst (I.inst0 .one))) (.or δ ψ)).shift = Ξ at hΞs hΞW hΞχ ⊢
  have hδ1 : δ.shift.Scoped (Ψ + 1) := scoped_shift H.hδ
  have hψ1 : ψ.shift.Scoped (Ψ + 1) := scoped_shift H.hψ
  have hX1s : (cof Ξ δ.shift).Scoped (Ψ + 1) := ⟨hΞs, hδ1⟩
  have hX2s : (cof Ξ ψ.shift).Scoped (Ψ + 1) := ⟨hΞs, hψ1⟩
  have hX3s : (cof (cof Ξ δ.shift) ψ.shift).Scoped (Ψ + 1) := ⟨hX1s, hψ1⟩
  have hX1 : I.Entails (cof Ξ δ.shift) (cof (cof Φ (φ.subst (I.inst0 .one))) δ).shift :=
    show I.Entails _ (.and _ _) from ent_and_mono hΞW (ent_refl _)
  have hX2 : I.Entails (cof Ξ ψ.shift) (cof (cof Φ (φ.subst (I.inst0 .one))) ψ).shift :=
    show I.Entails _ (.and _ _) from ent_and_mono hΞW (ent_refl _)
  have hX3 : I.Entails (cof (cof Ξ δ.shift) ψ.shift) (cof (cof (cof Φ (φ.subst (I.inst0 .one))) δ) ψ).shift :=
    show I.Entails _ (.and _ _) from ent_and_mono hX1 (ent_refl _)
  have hb1 := papp_pathC (HasTy0.restrict hX1s hX1 hd) hv0
  have hb2 := papp_pathC (HasTy0.restrict hX2s hX2 hp) hv0
  have ho := EqTm0.papp (EqTm0.restrict hX3s hX3 he) hv0 hv0 (I_eq_refl _)
  rw [dshift_dinst] at ho
  exact HasTy0.split hδ1 hψ1 hΞχ (HasTy0.restrict hΞs hΞW (HasTy0.dwk H.hS H.hfib)) hb1 hb2 ho

theorem hext : HasTy0 S Ψ (cof Φ (φ.subst (I.inst0 .one))) Γ (tgExt A φ T e ψ u0 δ) (tgFib A φ T e ψ u0) := by
  have hΞs : (cof (cof Φ (φ.subst (I.inst0 .one))) (.or δ ψ)).Scoped Ψ := ⟨H.hWs, ⟨H.hδ, H.hψ⟩⟩
  have hs0 := HasTy0.dsubst H.hS H.hpsys (r := .zero) trivial
  rw [dshift_dinst, psys_dinst] at hs0
  have hside : EqTm0 S Ψ (cof (cof Φ (φ.subst (I.inst0 .one))) (.or δ ψ)) Γ
      ((split δ.shift (papp (tgPd A φ T e ψ u0).dshift (.var 0)) ψ.shift
        (papp (tgPpsi A φ e ψ u0).dshift (.var 0))).dinst .zero) (fst (tgC A φ e ψ u0)) (tgFib A φ T e ψ u0) := by
    rw [psys_dinst]
    refine EqTm0.local (φ := δ) (ψ := ψ) H.hδ H.hψ (ent_and_right _ _) hs0
      (HasTy0.restrict hΞs (ent_and_left _ _) H.hfc) ?_ ?_
    · have hX : (cof (cof (cof Φ (φ.subst (I.inst0 .one))) (.or δ ψ)) δ).Scoped Ψ := ⟨hΞs, H.hδ⟩
      exact EqTm0.trans (EqTm0.splitL (ent_and_right _ _) (HasTy0.restrict hX (ent_and_left _ _) hs0))
        (pathC_zero (HasTy0.restrict hX (ent_and_mono (ent_and_left _ _) (ent_refl _)) H.hPd))
    · have hX : (cof (cof (cof Φ (φ.subst (I.inst0 .one))) (.or δ ψ)) ψ).Scoped Ψ := ⟨hΞs, H.hψ⟩
      exact EqTm0.trans (EqTm0.splitR (ent_and_right _ _) (HasTy0.restrict hX (ent_and_left _ _) hs0))
        (pathC_zero (HasTy0.restrict hX (ent_and_mono (ent_and_left _ _) (ent_refl _)) H.hPψ))
  rw [tgExt_eq]
  exact HasTy0.hcomp H.hfib ⟨H.hδ, H.hψ⟩ H.hpsys H.hfc hside

/-- On `ψ` the extension is `(u0, ⟨_⟩ a1')`. -/
theorem hextψ : EqTm0 S Ψ (cof (cof Φ (φ.subst (I.inst0 .one))) ψ) Γ (tgExt A φ T e ψ u0 δ)
    (pair u0 (plam (tgA1' A φ e ψ u0).dshift)) (tgFib A φ T e ψ u0) := by
  have hX := HasTy0.restrict H.hWψs (ent_and_left _ _) H.hext
  rw [tgExt_eq] at hX ⊢
  have e1 := EqTm0.hcompFace (ent_trans (ent_and_right _ _) (ent_or_right _ _)) hX
  have hs1 := HasTy0.dsubst H.hS H.hpsys (r := .one) trivial
  rw [dshift_dinst] at hs1
  have hs1' := HasTy0.restrict H.hWψs (ent_and_intro (ent_and_left _ _) (ent_trans (ent_and_right _ _) (ent_or_right _ _))) hs1
  rw [psys_dinst] at e1 hs1'
  exact EqTm0.trans e1 (EqTm0.trans (EqTm0.splitR (ent_and_right _ _) hs1') (pathC_one H.hPψ))

/-! ### The base of the result -/

theorem hfext : HasTy0 S Ψ (cof Φ (φ.subst (I.inst0 .one))) Γ (fst (tgExt A φ T e ψ u0 δ)) (T.dinst .one) := by
  have := H.hext; rw [tgFib_eq] at this; exact HasTy0.fst this

theorem hsext : HasTy0 S Ψ (cof Φ (φ.subst (I.inst0 .one))) Γ (snd (tgExt A φ T e ψ u0 δ))
    (pathC (A.dinst .one) (app (fst (e.dinst .one)) (fst (tgExt A φ T e ψ u0 δ))) (tgA1' A φ e ψ u0)) := by
  have := H.hext; rw [tgFib_eq] at this
  have h := HasTy0.snd this; rwa [P_inst] at h

theorem hsextψ : EqTm0 S Ψ (cof (cof Φ (φ.subst (I.inst0 .one))) ψ) Γ (snd (tgExt A φ T e ψ u0 δ))
    (plam (tgA1' A φ e ψ u0).dshift)
    (pathC (A.dinst .one) (app (fst (e.dinst .one)) (fst (tgExt A φ T e ψ u0 δ))) (tgA1' A φ e ψ u0)) := by
  have hX : I.Entails (cof (cof Φ (φ.subst (I.inst0 .one))) ψ) Φ := ent_trans (ent_and_left _ _) (ent_and_left _ _)
  have he := H.hextψ
  have hp := H.hpψ
  rw [tgFib_eq] at he hp
  have e1 := EqTm0.snd he
  rw [P_inst] at e1
  have hsp := HasTy0.snd hp
  rw [P_inst] at hsp
  have e2 := EqTm0.sndBeta hsp
  have hfe := EqTm0.fst he
  have hA1 := H.hA1X H.hWψs hX
  have ha1 := HasTy0.restrict H.hWψs hX H.ha1'
  have he1 := H.he1W H.hWψs (ent_and_left _ _)
  have eP : EqTm0 S Ψ (cof (cof Φ (φ.subst (I.inst0 .one))) ψ) Γ
      (pathC (A.dinst .one) (app (fst (e.dinst .one)) (fst (pair u0 (plam (tgA1' A φ e ψ u0).dshift))))
        (tgA1' A φ e ψ u0))
      (pathC (A.dinst .one) (app (fst (e.dinst .one)) (fst (tgExt A φ T e ψ u0 δ))) (tgA1' A φ e ψ u0)) (univ l) :=
    EqTm0.path (EqTm0.refl (HasTy0.dwk H.hS hA1))
      (by rw [dshift_dinst]; exact app_fst_congr he1 (EqTm0.symm hfe))
      (by rw [dshift_dinst]; exact EqTm0.refl ha1)
  exact EqTm0.trans e1 (EqTm0.conv e2 eP)

theorem hasys : HasTy0 S (Ψ + 1) (cof Φ (.or (φ.subst (I.inst0 .one)) ψ)).shift Γ.dshift
    (split (φ.subst (I.inst0 .one)).shift (papp (snd (tgExt A φ T e ψ u0 δ)).dshift (.neg (.var 0)))
      ψ.shift (tgA1' A φ e ψ u0).dshift) (A.dinst .one).dshift := by
  have hv0 : (I.var 0).Scoped (Ψ + 1) := show 0 < Ψ + 1 by omega
  have hφ1 : (φ.subst (I.inst0 .one)).Scoped Ψ := H.hφr (r := .one) trivial
  have hΞs : (cof Φ (.or (φ.subst (I.inst0 .one)) ψ)).shift.Scoped (Ψ + 1) := scoped_shift ⟨H.hs, ⟨hφ1, H.hψ⟩⟩
  have hΞΦ : I.Entails (cof Φ (.or (φ.subst (I.inst0 .one)) ψ)).shift Φ.shift := ent_shift (ent_and_left _ _)
  have hΞχ : I.Entails (cof Φ (.or (φ.subst (I.inst0 .one)) ψ)).shift
      (.or (φ.subst (I.inst0 .one)).shift ψ.shift) := ent_shift (ent_and_right _ (.or _ ψ))
  have hd := HasTy0.dwk H.hS H.hsext
  rw [pathC_dshift] at hd
  have he := EqTm0.dwk H.hS H.hsextψ
  rw [pathC_dshift, plam_dshift_dshift] at he
  have hpl := HasTy0.dwk H.hS H.hpl
  rw [pathC_dshift, plam_dshift_dshift] at hpl
  have hA1 := HasTy0.dwk H.hS (H.hAr (r := .one) trivial)
  have ha1 := HasTy0.dwk H.hS H.ha1'
  generalize (cof Φ (.or (φ.subst (I.inst0 .one)) ψ)).shift = Ξ at hΞs hΞΦ hΞχ ⊢
  have hφ1s : (φ.subst (I.inst0 .one)).shift.Scoped (Ψ + 1) := scoped_shift hφ1
  have hψ1 : ψ.shift.Scoped (Ψ + 1) := scoped_shift H.hψ
  have hX1s : (cof Ξ (φ.subst (I.inst0 .one)).shift).Scoped (Ψ + 1) := ⟨hΞs, hφ1s⟩
  have hX2s : (cof Ξ ψ.shift).Scoped (Ψ + 1) := ⟨hΞs, hψ1⟩
  have hX3s : (cof (cof Ξ (φ.subst (I.inst0 .one)).shift) ψ.shift).Scoped (Ψ + 1) := ⟨hX1s, hψ1⟩
  have hX1 : I.Entails (cof Ξ (φ.subst (I.inst0 .one)).shift) (cof Φ (φ.subst (I.inst0 .one))).shift :=
    show I.Entails _ (.and _ _) from ent_and_mono hΞΦ (ent_refl _)
  have hX3 : I.Entails (cof (cof Ξ (φ.subst (I.inst0 .one)).shift) ψ.shift)
      (cof (cof Φ (φ.subst (I.inst0 .one))) ψ).shift :=
    show I.Entails _ (.and _ _) from ent_and_mono hX1 (ent_refl _)
  have hneg : (I.neg (.var 0)).Scoped (Ψ + 1) := hv0
  have hb1 := papp_pathC (HasTy0.restrict hX1s hX1 hd) hneg
  have hb2 := HasTy0.restrict hX2s (ent_trans (ent_and_left _ _) hΞΦ) ha1
  have e1 := EqTm0.papp (EqTm0.restrict hX3s hX3 he) hneg hneg (I_eq_refl _)
  rw [dshift_dinst] at e1
  have hpp := papp_pathC (HasTy0.restrict hX3s hX3 hpl) hneg
  have e2 := EqTm0.pathBeta hpp
  rw [dshift_dinst] at e2
  exact HasTy0.split hφ1s hψ1 hΞχ (HasTy0.restrict hΞs hΞΦ hA1) hb1 hb2 (EqTm0.trans e1 e2)

theorem ha1 : HasTy0 S Ψ Φ Γ (tgA1 A φ T e ψ u0 δ) (A.dinst .one) := by
  have hφ1 : (φ.subst (I.inst0 .one)).Scoped Ψ := H.hφr (r := .one) trivial
  have hΞs : (cof Φ (.or (φ.subst (I.inst0 .one)) ψ)).Scoped Ψ := ⟨H.hs, ⟨hφ1, H.hψ⟩⟩
  have hs0 := HasTy0.dsubst H.hS H.hasys (r := .zero) trivial
  rw [dshift_dinst, asys_dinst] at hs0
  have hside : EqTm0 S Ψ (cof Φ (.or (φ.subst (I.inst0 .one)) ψ)) Γ
      ((split (φ.subst (I.inst0 .one)).shift (papp (snd (tgExt A φ T e ψ u0 δ)).dshift (.neg (.var 0)))
        ψ.shift (tgA1' A φ e ψ u0).dshift).dinst .zero) (tgA1' A φ e ψ u0) (A.dinst .one) := by
    rw [asys_dinst]
    refine EqTm0.local (φ := φ.subst (I.inst0 .one)) (ψ := ψ) hφ1 H.hψ (ent_and_right _ _) hs0
      (HasTy0.restrict hΞs (ent_and_left _ _) H.ha1') ?_ ?_
    · have hX : (cof (cof Φ (.or (φ.subst (I.inst0 .one)) ψ)) (φ.subst (I.inst0 .one))).Scoped Ψ := ⟨hΞs, hφ1⟩
      have hsx := HasTy0.restrict hX (ent_and_mono (ent_and_left _ _) (ent_refl _)) H.hsext
      exact EqTm0.trans (EqTm0.splitL (ent_and_right _ _) (HasTy0.restrict hX (ent_and_left _ _) hs0))
        (EqTm0.trans (papp_pathC_eq hsx (r := .neg .zero) (r' := .one) trivial trivial I_eq_neg_zero) (pathC_one hsx))
    · have hX : (cof (cof Φ (.or (φ.subst (I.inst0 .one)) ψ)) ψ).Scoped Ψ := ⟨hΞs, H.hψ⟩
      exact EqTm0.splitR (ent_and_right _ _) (HasTy0.restrict hX (ent_and_left _ _) hs0)
  rw [tgA1_eq]
  exact HasTy0.hcomp (H.hAr (r := .one) trivial) ⟨hφ1, H.hψ⟩ H.hasys H.ha1' hside

theorem hglueSide : EqTm0 S Ψ (cof Φ (φ.subst (I.inst0 .one))) Γ (app (fst (e.dinst .one)) (fst (tgExt A φ T e ψ u0 δ)))
    (tgA1 A φ T e ψ u0 δ) (A.dinst .one) := by
  have hW := HasTy0.restrict H.hWs (ent_and_left _ _) H.ha1
  rw [tgA1_eq] at hW ⊢
  have hWχ : I.Entails (cof Φ (φ.subst (I.inst0 .one))) (.or (φ.subst (I.inst0 .one)) ψ) :=
    ent_trans (ent_and_right _ _) (ent_or_left _ _)
  have e1 := EqTm0.hcompFace hWχ hW
  have hs1 := HasTy0.dsubst H.hS H.hasys (r := .one) trivial
  rw [dshift_dinst] at hs1
  have hs1' := HasTy0.restrict H.hWs (ent_and_intro (ent_and_left _ _) hWχ) hs1
  rw [asys_dinst] at e1 hs1'
  have e2 := EqTm0.splitL (ent_and_right _ _) hs1'
  have e3 := papp_pathC_eq H.hsext (r := .neg .one) (r' := .zero) trivial trivial I_eq_neg_one
  exact EqTm0.symm (EqTm0.trans e1 (EqTm0.trans e2 (EqTm0.trans e3 (pathC_zero H.hsext))))

/-- The contractum is typed at the end of the line. -/
theorem typed : HasTy0 S Ψ Φ Γ (transpGlueWith δ A φ T e ψ u0) ((glue A φ T e).dinst .one) := by
  rw [transpGlueWith_eq, glue_dinst]
  exact HasTy0.glueEl (H.hGr (r := .one) trivial) H.he1 H.hfext H.ha1 H.hglueSide

end TG

end KubusCore.Meta
