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

end TG

end KubusCore.Meta
