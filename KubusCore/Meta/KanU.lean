import KubusCore.Meta.KanGlue
import KubusCore.Meta.KanFill

/-!
# Metatheory: typing of equivalences, `lineEquiv`, and the contractum of `hcomp` in `U`
-/

namespace KubusCore.Meta

open Tm

variable {S : Sig}

theorem arrow_shift (T A : Tm) : (arrow T A).shift = arrow T.shift A.shift := by
  simp only [arrow, Tm.shift, Tm.ren, ren_ren]; rfl

theorem shift2_lookup1 (X : Tm) (Γ : Ctx) : Ctx.lookup (X.shift :: X :: Γ) 1 = some X.shift.shift := rfl

section
variable (hS : SigClosed S)
include hS

theorem pathC_typed {Ψ Φ Γ A a b l} (hA : HasTy0 S Ψ Φ Γ A (univ l)) (ha : HasTy0 S Ψ Φ Γ a A)
    (hb : HasTy0 S Ψ Φ Γ b A) : HasTy0 S Ψ Φ Γ (pathC A a b) (univ l) := by
  have hAd := HasTy0.dwk hS hA
  exact HasTy0.path hAd (by rw [dshift_dinst]; exact ha) (by rw [dshift_dinst]; exact hb)

theorem isContr_typed {Ψ Φ Γ X l} (hX : HasTy0 S Ψ Φ Γ X (univ l)) :
    HasTy0 S Ψ Φ Γ (isContr X) (univ l) := by
  have hX1 := HasTy0.wk hS hX hX
  have hX2 := HasTy0.wk hS hX1 hX1
  have hv1 : HasTy0 S Ψ Φ (X.shift :: X :: Γ) (var 1) X.shift.shift :=
    HasTy0.var (Wf0.cons hX1) rfl
  have hv0 : HasTy0 S Ψ Φ (X.shift :: X :: Γ) (var 0) X.shift.shift :=
    HasTy0.var (Wf0.cons hX1) rfl
  exact HasTy0.sigma hX (HasTy0.pi hX1 (pathC_typed hS hX2 hv1 hv0))

theorem fiber_typed {Ψ Φ Γ T A f y l} (hT : HasTy0 S Ψ Φ Γ T (univ l)) (hA : HasTy0 S Ψ Φ Γ A (univ l))
    (hf : HasTy0 S Ψ Φ Γ f (arrow T A)) (hy : HasTy0 S Ψ Φ Γ y A) :
    HasTy0 S Ψ Φ Γ (fiber T A f y) (univ l) := by
  have hA1 := HasTy0.wk hS hT hA
  have hf1 := HasTy0.wk hS hT hf
  rw [arrow_shift] at hf1
  have hv : HasTy0 S Ψ Φ (T :: Γ) (var 0) T.shift := HasTy0.var (Wf0.cons hT) rfl
  have happ := HasTy0.app hf1 hv
  rw [shift_inst] at happ
  exact HasTy0.sigma hT (pathC_typed hS hA1 happ (HasTy0.wk hS hT hy))

theorem isEquiv_typed {Ψ Φ Γ T A f l} (hT : HasTy0 S Ψ Φ Γ T (univ l)) (hA : HasTy0 S Ψ Φ Γ A (univ l))
    (hf : HasTy0 S Ψ Φ Γ f (arrow T A)) : HasTy0 S Ψ Φ Γ (isEquiv T A f) (univ l) := by
  have hT1 := HasTy0.wk hS hA hT
  have hA1 := HasTy0.wk hS hA hA
  have hf1 := HasTy0.wk hS hA hf
  rw [arrow_shift] at hf1
  have hv : HasTy0 S Ψ Φ (A :: Γ) (var 0) A.shift := HasTy0.var (Wf0.cons hA) rfl
  exact HasTy0.pi hA (isContr_typed hS (fiber_typed hS hT1 hA1 hf1 hv))

theorem arrow_typed {Ψ Φ Γ T A l} (hT : HasTy0 S Ψ Φ Γ T (univ l)) (hA : HasTy0 S Ψ Φ Γ A (univ l)) :
    HasTy0 S Ψ Φ Γ (arrow T A) (univ l) := HasTy0.pi hT (HasTy0.wk hS hT hA)

theorem equiv_typed {Ψ Φ Γ T A l} (hT : HasTy0 S Ψ Φ Γ T (univ l)) (hA : HasTy0 S Ψ Φ Γ A (univ l)) :
    HasTy0 S Ψ Φ Γ (equiv T A) (univ l) := by
  have hTA := arrow_typed hS hT hA
  have hv : HasTy0 S Ψ Φ (arrow T A :: Γ) (var 0) (arrow T A).shift := HasTy0.var (Wf0.cons hTA) rfl
  rw [arrow_shift] at hv
  exact HasTy0.sigma hTA (isEquiv_typed hS (HasTy0.wk hS hTA hT) (HasTy0.wk hS hTA hA) hv)

end


/-! ## The transport filler with a constant cofibration -/

theorem tf_L1 (C : Tm) : (C.dsubst (bind2 (.and (.var 1) (.var 0)))).dset 1 (I.ofDir false) =
    C.subst Tm.var (sk (.and .zero (.var 0)) 2) := by ssub
theorem tf_L0s (C : Tm) : ((C.dsubst (bind2 (.and (.var 1) (.var 0)))).dinst .zero).dshift =
    C.subst Tm.var (sk (.and (.var 1) .zero) 2) := by ssub
theorem tf_L0s1 (C : Tm) : (C.subst Tm.var (sk (.and (.var 1) .zero) 2)).dset 1 (I.ofDir false) =
    C.subst Tm.var (sk (.and .zero .zero) 2) := by ssub
theorem tf_L0 (C : Tm) : (C.dsubst (bind2 (.and (.var 1) (.var 0)))).dinst .zero =
    C.subst Tm.var (sk (.and (.var 0) .zero) 1) := by ssub
theorem tf_L1' (C : Tm) : (C.dsubst (bind2 (.and (.var 1) (.var 0)))).dinst .one =
    C.subst Tm.var (sk (.and (.var 0) .one) 1) := by ssub

/-- `transp (j. C(i ∧ j)) (i = 0) a`, a filler from `C(0)` to `C(i)` that is `a` at `i = 0`. -/
def tfill (C a : Tm) : Tm := transp (C.dsubst (bind2 (.and (.var 1) (.var 0)))) (.neg (.var 0)) a.dshift

theorem tfill_typed (hS : SigClosed S) {Ψ Φ Δ C a l}
    (hC : HasTy0 S (Ψ + 1) Φ.shift Δ.dshift C (univ l)) (ha : HasTy0 S Ψ Φ Δ a (C.dinst .zero)) :
    HasTy0 S (Ψ + 1) Φ.shift Δ.dshift (tfill C a) C ∧
      EqTm0 S Ψ Φ Δ ((tfill C a).dinst .zero) a (C.dinst .zero) := by
  have hw0 := wf_unshift hS (wf_of_ty hC)
  have hs := scoped_of_wf hw0
  have hv0 : (I.var 0).Scoped (Ψ + 1) := show 0 < Ψ + 1 by omega
  have hv1 : (I.var 1).Scoped (Ψ + 1 + 1) := show 1 < Ψ + 1 + 1 by omega
  have hv0' : (I.var 0).Scoped (Ψ + 1 + 1) := show 0 < Ψ + 1 + 1 by omega
  have hL : HasTy0 S (Ψ + 1 + 1) Φ.shift.shift Δ.dshift.dshift
      (C.dsubst (bind2 (.and (.var 1) (.var 0)))) (univ l) := by
    have := HasTy0.isub hS (τ := bind2 (.and (.var 1) (.var 0))) hC
      (fun i hi => by rcases i with _ | i
                      · exact ⟨hv1, hv0'⟩
                      · show i + 2 < Ψ + 1 + 1; omega)
      (ent_bind2_shift _ (ent_refl _))
      (by rw [ctxI_bind2]; exact hw0.dwk2 hS)
    rwa [ctxI_bind2] at this
  have hXs : (cof Φ.shift (.neg (.var 0))).shift.Scoped (Ψ + 1 + 1) :=
    scoped_shift ⟨scoped_shift hs, hv0⟩
  have hYX : I.Entails (cof Φ.shift (.neg (.var 0))).shift Φ.shift.shift := ent_shift (ent_and_left _ _)
  have hY1 : I.Entails (cof Φ.shift (.neg (.var 0))).shift (I.lit 1 false) :=
    ent_shift (ent_and_right _ (.neg (.var 0)))
  have hYΦ : I.Entails (cof Φ.shift (.neg (.var 0))).shift (Φ.subst (fun n => .var (n + 2))) := by
    rw [I_add2]; exact hYX
  have hwY : Wf0 S (Ψ + 1 + 1) (cof Φ.shift (.neg (.var 0))).shift (ctxI (fun n => .var (n + 2)) Δ) := by
    rw [ctxI_add2]; exact (hw0.dwk2 hS).restrict hXs hYX
  have hconst : EqTm0 S (Ψ + 1 + 1) (cof Φ.shift (.neg (.var 0))).shift Δ.dshift.dshift
      (C.dsubst (bind2 (.and (.var 1) (.var 0))))
      ((C.dsubst (bind2 (.and (.var 1) (.var 0)))).dinst .zero).dshift (univ l) := by
    have hLY := HasTy0.restrict hXs hYX hL
    have e1 := EqTm0.faceU (i := 1) (d := false) hv1 hY1 hLY
    rw [tf_L1] at e1
    have e2 := line_ieq hS hC (k := 2) (Ψ' := Ψ + 1 + 1) (r := .and .zero (.var 0)) (r' := .zero) hYΦ
      ⟨trivial, hv0'⟩ trivial (by omega) (I_eq_and_zero _) hwY
    rw [ctxI_add2] at e2
    have hL0 := HasTy0.restrict hXs hYX (HasTy0.dwk hS (HasTy0.dsubst hS (Φ := Φ.shift) (Γ := Δ.dshift) hL (r := .zero) trivial))
    rw [tf_L0s] at hL0
    have e3 := EqTm0.faceU (i := 1) (d := false) hv1 hY1 hL0
    rw [tf_L0s1] at e3
    have e4 := line_ieq hS hC (k := 2) (Ψ' := Ψ + 1 + 1) (r := .and .zero .zero) (r' := .zero) hYΦ
      ⟨trivial, trivial⟩ trivial (by omega) (I_eq_and_zero _) hwY
    rw [ctxI_add2] at e4
    rw [tf_L0s]
    exact EqTm0.trans e1 (EqTm0.trans e2 (EqTm0.symm (EqTm0.trans e3 e4)))
  have hwX : Wf0 S (Ψ + 1) Φ.shift (ctxI (fun n => .var (n + 1)) Δ) := by
    rw [ctxI_add1]; exact wf_of_ty hC
  have ha' : HasTy0 S (Ψ + 1) Φ.shift Δ.dshift a.dshift
      ((C.dsubst (bind2 (.and (.var 1) (.var 0)))).dinst .zero) := by
    rw [tf_L0]
    have e := line_ieq hS hC (k := 1) (Ψ' := Ψ + 1) (r := .zero) (r' := .and (.var 0) .zero) (ent_refl _) trivial
      ⟨hv0, trivial⟩ (by omega) (I_eq_symm (I_eq_and_zero_r _)) hwX
    rw [ctxI_add1, sk_zero1] at e
    exact HasTy0.conv (HasTy0.dwk hS ha) e
  have ht0 := HasTy0.transp hL (show (I.neg (.var 0)).Scoped (Ψ + 1) from hv0) hconst ha'
  have eC : EqTm0 S (Ψ + 1) Φ.shift Δ.dshift ((C.dsubst (bind2 (.and (.var 1) (.var 0)))).dinst .one) C (univ l) := by
    have e := line_ieq hS hC (k := 1) (Ψ' := Ψ + 1) (r := .and (.var 0) .one) (r' := .var 0) (ent_refl _)
      ⟨hv0, trivial⟩ hv0 (by omega) (I_eq_and_one_r _) hwX
    rw [ctxI_add1, sk_var1] at e
    rw [tf_L1']; exact e
  refine ⟨HasTy0.conv ht0 eC, ?_⟩
  have h0 := HasTy0.dsubst hS ht0 (r := .zero) trivial
  have eC0 := EqTm0.dsubst hS eC (r := .zero) trivial
  have hf := EqTm0.transpFace (ent_negzero Φ) (show HasTy0 S Ψ Φ Δ (transp ((C.dsubst (bind2 (.and (.var 1) (.var 0)))).subst
    (fun n => (Tm.var n).dshift) (I.up (I.inst0 .zero))) (I.neg .zero) (a.dshift.dinst .zero)) _ from h0)
  have hf' : EqTm0 S Ψ Φ Δ ((tfill C a).dinst .zero) (a.dshift.dinst .zero) _ := hf
  rw [dshift_dinst] at hf'
  exact EqTm0.conv hf' eC0


theorem lam_dinst (A t : Tm) (r : I) : (lam A t).dinst r = lam (A.dinst r) (t.dinst r) := by
  simp only [Tm.dinst, Tm.dsubst, Tm.subst, up_var]

theorem lineFun_eq (B : Tm) : lineFun B = lam (B.dinst .zero).dshift (tfill B.shift (var 0)) := rfl

/-- `lineFun B : B(0) → B(i)`, and at `i = 0` it is the identity. -/
theorem lineFun_typed (hS : SigClosed S) {Ψ Φ Γ B l} (hB : HasTy0 S (Ψ + 1) Φ.shift Γ.dshift B (univ l)) :
    HasTy0 S (Ψ + 1) Φ.shift Γ.dshift (lineFun B) (arrow (B.dinst .zero).dshift B) ∧
      EqTm0 S Ψ Φ Γ ((lineFun B).dinst .zero) (lam (B.dinst .zero) (var 0))
        (arrow (B.dinst .zero) (B.dinst .zero)) := by
  have hB0 := HasTy0.dsubst hS hB (r := .zero) trivial
  have hB0d := HasTy0.dwk hS hB0
  have hC : HasTy0 S (Ψ + 1) Φ.shift (Ctx.dshift (B.dinst .zero :: Γ)) B.shift (univ l) := HasTy0.wk hS hB0d hB
  have ha : HasTy0 S Ψ Φ (B.dinst .zero :: Γ) (var 0) (B.shift.dinst .zero) := by
    rw [shift_dinst_comm]; exact HasTy0.var (Wf0.cons hB0) rfl
  obtain ⟨ht, he⟩ := tfill_typed hS hC ha
  have hpi : HasTy0 S (Ψ + 1) Φ.shift Γ.dshift (pi (B.dinst .zero).dshift B.shift) (univ l) :=
    HasTy0.pi hB0d (HasTy0.wk hS hB0d hB)
  refine ⟨HasTy0.lam hpi ht, ?_⟩
  rw [lineFun_eq, lam_dinst, dshift_dinst]
  rw [shift_dinst_comm] at he
  exact EqTm0.lam (HasTy0.pi hB0 (HasTy0.wk hS hB0 hB0)) he


/-! ## Equations -/
def center (y : Tm) : Tm := pair y (plam y.dshift)
theorem pathC_shift (A a b : Tm) : (pathC A a b).shift = pathC A.shift a.shift b.shift := by
  simp only [pathC]; scalc
theorem pathC_dshift (A a b : Tm) : (pathC A a b).dshift = pathC A.dshift a.dshift b.dshift := by
  simp only [pathC]; scalc
theorem pathC_dinst (A a b : Tm) (r : I) : (pathC A a b).dinst r = pathC (A.dinst r) (a.dinst r) (b.dinst r) := by
  simp only [pathC]; scalc
theorem P_inst (A g b a : Tm) : (pathC A.shift (app g.shift (var 0)) b.shift).inst a = pathC A (app g a) b := by
  simp only [pathC]; scalc
theorem fiber_shift (T A f y : Tm) : (fiber T A f y).shift = fiber T.shift A.shift f.shift y.shift := by
  simp only [fiber, pathC]; scalc
theorem fiber_dshift (T A f y : Tm) : (fiber T A f y).dshift = fiber T.dshift A.dshift f.dshift y.dshift := by
  simp only [fiber, pathC]; scalc
theorem center_shift (y : Tm) : (center y).shift = center y.shift := by
  simp only [center]; scalc
theorem arrow_dshift (T A : Tm) : (arrow T A).dshift = arrow T.dshift A.dshift := by
  simp only [arrow]; scalc
theorem lamid_shift (T : Tm) : (lam T (var 0)).shift = lam T.shift (var 0) := by scalc
theorem lamid_dshift (T : Tm) : (lam T (var 0)).dshift = lam T.dshift (var 0) := by scalc
theorem K_inst (X c : Tm) : (pi X.shift (pathC X.shift.shift (var 1) (var 0))).inst c = pi X (pathC X.shift c.shift (var 0)) := by
  simp only [pathC]; scalc
theorem idIsEquiv_eq (T f : Tm) : idIsEquiv T f = lam T (pair (center (var 0))
    (lam (fiber T.shift T.shift f.shift (var 0))
      (plam (pair (papp (snd (var 0)) (.neg (.var 0)))
        (plam (papp (snd (var 0)) (.or (.neg (.var 1)) (.var 0)))))))) := rfl
theorem isEquiv_eq (T A f : Tm) : isEquiv T A f = pi A (isContr (fiber T.shift A.shift f.shift (var 0))) := rfl
theorem isEquiv_dinst (T A f : Tm) (r : I) : (isEquiv T A f).dinst r = isEquiv (T.dinst r) (A.dinst r) (f.dinst r) := by
  simp only [isEquiv, isContr, fiber, pathC]; scalc
theorem isEquiv_inst (T A : Tm) (a : Tm) : (isEquiv T.shift A.shift (var 0)).inst a = isEquiv T A a := by
  simp only [isEquiv, isContr, fiber, pathC]; scalc
theorem arrow_dinst (T A : Tm) (r : I) : (arrow T A).dinst r = arrow (T.dinst r) (A.dinst r) := by
  simp only [arrow]; scalc

theorem app_dshift_dinst (f a : Tm) (r : I) : (app f.dshift a).dinst r = app f (a.dinst r) := by
  show app (f.dshift.dinst r) (a.dinst r) = _; rw [dshift_dinst]

theorem I_eq_neg_zero : I.Eq (.neg .zero) .one := fun _ => rfl
theorem I_eq_neg_one : I.Eq (.neg .one) .zero := fun _ => rfl
theorem I_eq_or_negzero (r : I) : I.Eq (.or (.neg .zero) r) .one := fun ρ => by
  cases h : r.eval ρ <;> simp [I.eval, h] <;> rfl
theorem I_eq_or_negone (r : I) : I.Eq (.or (.neg .one) r) r := fun ρ => by
  cases h : r.eval ρ <;> simp [I.eval, h] <;> rfl

/-! ## The identity is an equivalence -/

/-- `f : T → T` is judgmentally the identity. -/
structure IsId (S : Sig) (Ψ : Nat) (Φ : I) (Γ : Ctx) (T f : Tm) (l : Nat) : Prop where
  ty : HasTy0 S Ψ Φ Γ T (univ l)
  fn : HasTy0 S Ψ Φ Γ f (arrow T T)
  id : EqTm0 S Ψ Φ Γ f (lam T (var 0)) (arrow T T)

theorem IsId.wk (hS : SigClosed S) {Ψ Φ Γ T f l B l'} (h : IsId S Ψ Φ Γ T f l)
    (hB : HasTy0 S Ψ Φ Γ B (univ l')) : IsId S Ψ Φ (B :: Γ) T.shift f.shift l where
  ty := HasTy0.wk hS hB h.ty
  fn := by have := HasTy0.wk hS hB h.fn; rwa [arrow_shift] at this
  id := by have := EqTm0.wk hS hB h.id; rwa [lamid_shift, arrow_shift] at this

theorem IsId.dwk (hS : SigClosed S) {Ψ Φ Γ T f l} (h : IsId S Ψ Φ Γ T f l) :
    IsId S (Ψ + 1) Φ.shift Γ.dshift T.dshift f.dshift l where
  ty := HasTy0.dwk hS h.ty
  fn := by have := HasTy0.dwk hS h.fn; rwa [arrow_dshift] at this
  id := by have := EqTm0.dwk hS h.id; rwa [lamid_dshift, arrow_dshift] at this

theorem IsId.app_ty {Ψ Φ Γ T f l x} (h : IsId S Ψ Φ Γ T f l) (hx : HasTy0 S Ψ Φ Γ x T) :
    HasTy0 S Ψ Φ Γ (app f x) T := by
  have := HasTy0.app h.fn hx; rwa [shift_inst] at this

theorem IsId.app_eq (hS : SigClosed S) {Ψ Φ Γ T f l x} (h : IsId S Ψ Φ Γ T f l) (hx : HasTy0 S Ψ Φ Γ x T) :
    EqTm0 S Ψ Φ Γ (app f x) x T := by
  have hlam : HasTy0 S Ψ Φ Γ (lam T (var 0)) (arrow T T) :=
    HasTy0.lam (HasTy0.pi h.ty (HasTy0.wk hS h.ty h.ty)) (HasTy0.var (Wf0.cons h.ty) rfl)
  have e1 := EqTm0.app h.id (EqTm0.refl hx)
  have e2 := EqTm0.piBeta (HasTy0.app hlam hx)
  rw [shift_inst] at e1 e2
  exact EqTm0.trans e1 e2


theorem papp_pathC {Ψ Φ Γ p A a b r} (hp : HasTy0 S Ψ Φ Γ p (pathC A a b)) (hr : r.Scoped Ψ) :
    HasTy0 S Ψ Φ Γ (papp p r) A := by
  have := HasTy0.papp hp hr; rwa [dshift_dinst] at this

theorem papp_pathC_eq {Ψ Φ Γ p A a b r r'} (hp : HasTy0 S Ψ Φ Γ p (pathC A a b)) (hr : r.Scoped Ψ)
    (hr' : r'.Scoped Ψ) (he : I.Eq r r') : EqTm0 S Ψ Φ Γ (papp p r) (papp p r') A := by
  have := EqTm0.papp (EqTm0.refl hp) hr hr' he; rwa [dshift_dinst] at this

theorem pathC_one {Ψ Φ Γ p A a b} (hp : HasTy0 S Ψ Φ Γ p (pathC A a b)) :
    EqTm0 S Ψ Φ Γ (papp p .one) b A := by
  have := EqTm0.pathOne hp; rwa [dshift_dinst] at this

theorem pathC_zero {Ψ Φ Γ p A a b} (hp : HasTy0 S Ψ Φ Γ p (pathC A a b)) :
    EqTm0 S Ψ Φ Γ (papp p .zero) a A := by
  have := EqTm0.pathZero hp; rwa [dshift_dinst] at this

/-- A constant path `⟨_⟩ b : Path A a b`, given `a ≡ b`. -/
theorem plam_const (hS : SigClosed S) {Ψ Φ Γ A a b l} (hA : HasTy0 S Ψ Φ Γ A (univ l))
    (ha : HasTy0 S Ψ Φ Γ a A) (hb : HasTy0 S Ψ Φ Γ b A) (he : EqTm0 S Ψ Φ Γ b a A) :
    HasTy0 S Ψ Φ Γ (plam b.dshift) (pathC A a b) :=
  HasTy0.plam (pathC_typed hS hA ha hb) (HasTy0.dwk hS hb)
    (by rw [dshift_dinst, dshift_dinst]; exact he) (by rw [dshift_dinst, dshift_dinst]; exact EqTm0.refl hb)

theorem Q_typed (hS : SigClosed S) {Ψ Φ Δ T f y l} (h : IsId S Ψ Φ Δ T f l) (hy : HasTy0 S Ψ Φ Δ y T) :
    HasTy0 S Ψ Φ (T :: Δ) (pathC T.shift (app f.shift (var 0)) y.shift) (univ l) := by
  have h1 := h.wk hS h.ty
  have hv : HasTy0 S Ψ Φ (T :: Δ) (var 0) T.shift := HasTy0.var (Wf0.cons h.ty) rfl
  exact pathC_typed hS h1.ty (h1.app_ty hv) (HasTy0.wk hS h.ty hy)

theorem center_typed (hS : SigClosed S) {Ψ Φ Δ T f y l} (h : IsId S Ψ Φ Δ T f l) (hy : HasTy0 S Ψ Φ Δ y T) :
    HasTy0 S Ψ Φ Δ (center y) (fiber T T f y) :=
  HasTy0.pair (fiber_typed hS h.ty h.ty h.fn hy) hy (by
    rw [P_inst]; exact plam_const hS h.ty (h.app_ty hy) hy (EqTm0.symm (h.app_eq hS hy)))

theorem contr_typed (hS : SigClosed S) {Ψ Φ Δ T f y l} (h : IsId S Ψ Φ Δ T f l) (hy : HasTy0 S Ψ Φ Δ y T) :
    HasTy0 S Ψ Φ (fiber T T f y :: Δ)
      (plam (pair (papp (snd (var 0)) (.neg (.var 0)))
        (plam (papp (snd (var 0)) (.or (.neg (.var 1)) (.var 0))))))
      (pathC (fiber T T f y).shift (center y).shift (var 0)) := by
  have hF := fiber_typed hS h.ty h.ty h.fn hy
  have h2 := h.wk hS hF
  have hy2 := HasTy0.wk hS hF hy
  have hF2 := fiber_typed hS h2.ty h2.ty h2.fn hy2
  have hw : HasTy0 S Ψ Φ (fiber T T f y :: Δ) (var 0) (fiber T.shift T.shift f.shift y.shift) := by
    have := HasTy0.var (Wf0.cons hF) (x := 0) rfl; rwa [fiber_shift] at this
  have hfst := HasTy0.fst hw
  have hp : HasTy0 S Ψ Φ (fiber T T f y :: Δ) (snd (var 0))
      (pathC T.shift (app f.shift (fst (var 0))) y.shift) := by
    have := HasTy0.snd hw; rwa [P_inst] at this
  have h2d := h2.dwk hS
  have hy2d := HasTy0.dwk hS hy2
  have hp1 : HasTy0 S (Ψ + 1) Φ.shift (Ctx.dshift (fiber T T f y :: Δ)) (snd (var 0))
      (pathC T.shift.dshift (app f.shift (fst (var 0))).dshift y.shift.dshift) := by
    have := HasTy0.dwk hS hp; rw [pathC_dshift] at this; exact this
  have hp2 : HasTy0 S (Ψ + 1 + 1) Φ.shift.shift (Ctx.dshift (Ctx.dshift (fiber T T f y :: Δ))) (snd (var 0))
      (pathC T.shift.dshift.dshift (app f.shift (fst (var 0))).dshift.dshift y.shift.dshift.dshift) := by
    have := HasTy0.dwk hS hp1; rw [pathC_dshift] at this; exact this
  have hv0 : (I.var 0).Scoped (Ψ + 1) := show 0 < Ψ + 1 by omega
  have hv0' : (I.var 0).Scoped (Ψ + 1 + 1) := show 0 < Ψ + 1 + 1 by omega
  have hv1' : (I.var 1).Scoped (Ψ + 1 + 1) := show 1 < Ψ + 1 + 1 by omega
  have ha := papp_pathC hp1 (r := .neg (.var 0)) hv0
  -- the inner path, from `f (p(~i))` to `y`
  have hinner : HasTy0 S (Ψ + 1) Φ.shift (Ctx.dshift (fiber T T f y :: Δ))
      (plam (papp (snd (var 0)) (.or (.neg (.var 1)) (.var 0))))
      (pathC T.shift.dshift (app f.shift.dshift (papp (snd (var 0)) (.neg (.var 0)))) y.shift.dshift) := by
    refine HasTy0.plam (pathC_typed hS h2d.ty (h2d.app_ty ha) hy2d)
      (papp_pathC hp2 (r := .or (.neg (.var 1)) (.var 0)) ⟨hv1', hv0'⟩) ?_ ?_
    · show EqTm0 _ _ _ _ (papp (snd (var 0)) (.or (.neg (.var 0)) .zero)) _ _
      rw [dshift_dinst]
      exact EqTm0.trans (papp_pathC_eq hp1 (r' := .neg (.var 0)) ⟨hv0, trivial⟩ hv0 (I_eq_or_zero_r _))
        (EqTm0.symm (h2d.app_eq hS ha))
    · show EqTm0 _ _ _ _ (papp (snd (var 0)) (.or (.neg (.var 0)) .one)) _ _
      rw [dshift_dinst]
      exact EqTm0.trans (papp_pathC_eq hp1 (r' := .one) ⟨hv0, trivial⟩ trivial (I_eq_or_one_r _)) (pathC_one hp1)
  have hbody : HasTy0 S (Ψ + 1) Φ.shift (Ctx.dshift (fiber T T f y :: Δ))
      (pair (papp (snd (var 0)) (.neg (.var 0))) (plam (papp (snd (var 0)) (.or (.neg (.var 1)) (.var 0)))))
      (fiber T.shift.dshift T.shift.dshift f.shift.dshift y.shift.dshift) :=
    HasTy0.pair (fiber_typed hS h2d.ty h2d.ty h2d.fn hy2d) ha (by rw [P_inst]; exact hinner)
  have hQ := Q_typed hS h2 hy2
  -- endpoint `i = 0`: the centre
  have ha0 := papp_pathC hp (r := .neg .zero) trivial
  have ea0 : EqTm0 S Ψ Φ (fiber T T f y :: Δ) (papp (snd (var 0)) (.neg .zero)) y.shift T.shift :=
    EqTm0.trans (papp_pathC_eq hp (r' := .one) trivial trivial I_eq_neg_zero) (pathC_one hp)
  have hl0 : HasTy0 S Ψ Φ (fiber T T f y :: Δ) (plam (papp (snd (var 0)) (.or (.neg .zero) (.var 0))))
      (pathC T.shift (app f.shift (papp (snd (var 0)) (.neg .zero))) y.shift) := by
    have := HasTy0.dsubst hS hinner (r := .zero) trivial
    rw [pathC_dinst, dshift_dinst, dshift_dinst, app_dshift_dinst] at this; exact this
  have hpath0 := pathC_typed hS h2.ty (h2.app_ty ha0) hy2
  have hr0 : HasTy0 S Ψ Φ (fiber T T f y :: Δ) (plam y.shift.dshift)
      (pathC T.shift (app f.shift (papp (snd (var 0)) (.neg .zero))) y.shift) :=
    plam_const hS h2.ty (h2.app_ty ha0) hy2 (EqTm0.symm (EqTm0.trans (h2.app_eq hS ha0) ea0))
  have e0 : EqTm0 S Ψ Φ (fiber T T f y :: Δ)
      (pair (papp (snd (var 0)) (.neg .zero)) (plam (papp (snd (var 0)) (.or (.neg .zero) (.var 0)))))
      (center y.shift) (fiber T.shift T.shift f.shift y.shift) := by
    refine EqTm0.pair hF2 ea0 ?_
    rw [P_inst]
    refine EqTm0.plam hpath0 hl0 hr0 ?_
    exact EqTm0.trans (papp_pathC_eq hp1 (r' := .one) ⟨trivial, hv0⟩ trivial (I_eq_or_negzero _)) (pathC_one hp1)
  -- endpoint `i = 1`: the given point of the fibre
  have ha1 := papp_pathC hp (r := .neg .one) trivial
  have ea1 : EqTm0 S Ψ Φ (fiber T T f y :: Δ) (papp (snd (var 0)) (.neg .one)) (fst (var 0)) T.shift :=
    EqTm0.trans (papp_pathC_eq hp (r' := .zero) trivial trivial I_eq_neg_one)
      (EqTm0.trans (pathC_zero hp) (h2.app_eq hS hfst))
  have eQ := HasTy0.inst_congr hS hQ ha1 hfst ea1
  rw [P_inst, P_inst] at eQ
  have hl1 : HasTy0 S Ψ Φ (fiber T T f y :: Δ) (plam (papp (snd (var 0)) (.or (.neg .one) (.var 0))))
      (pathC T.shift (app f.shift (fst (var 0))) y.shift) := by
    have := HasTy0.dsubst hS hinner (r := .one) trivial
    rw [pathC_dinst, dshift_dinst, dshift_dinst, app_dshift_dinst] at this; exact HasTy0.conv this eQ
  have hr1 : HasTy0 S Ψ Φ (fiber T T f y :: Δ) (plam (papp (snd (var 0)).dshift (.var 0)))
      (pathC T.shift (app f.shift (fst (var 0))) y.shift) := by
    refine HasTy0.plam (pathC_typed hS h2.ty (h2.app_ty hfst) hy2) (papp_pathC hp1 hv0) ?_ ?_
    · show EqTm0 _ _ _ _ (papp (snd (var 0)) .zero) _ _; rw [dshift_dinst]; exact pathC_zero hp
    · show EqTm0 _ _ _ _ (papp (snd (var 0)) .one) _ _; rw [dshift_dinst]; exact pathC_one hp
  have eb1 : EqTm0 S Ψ Φ (fiber T T f y :: Δ) (plam (papp (snd (var 0)) (.or (.neg .one) (.var 0))))
      (snd (var 0)) (pathC T.shift (app f.shift (fst (var 0))) y.shift) :=
    EqTm0.trans (EqTm0.plam (pathC_typed hS h2.ty (h2.app_ty hfst) hy2) hl1 hr1
      (papp_pathC_eq hp1 (r' := .var 0) ⟨trivial, hv0⟩ hv0 (I_eq_or_negone _)))
      (EqTm0.symm (EqTm0.pathEta hp))
  have e1 : EqTm0 S Ψ Φ (fiber T T f y :: Δ)
      (pair (papp (snd (var 0)) (.neg .one)) (plam (papp (snd (var 0)) (.or (.neg .one) (.var 0)))))
      (var 0) (fiber T.shift T.shift f.shift y.shift) := by
    refine EqTm0.trans ?_ (EqTm0.symm (EqTm0.sigmaEta hw))
    refine EqTm0.pair hF2 ea1 ?_
    rw [P_inst]; exact EqTm0.conv eb1 (EqTm0.symm eQ)
  rw [fiber_shift, center_shift]
  refine HasTy0.plam (pathC_typed hS hF2 (center_typed hS h2 hy2) hw) (by rw [fiber_dshift]; exact hbody) ?_ ?_
  · rw [dshift_dinst]; exact e0
  · rw [dshift_dinst]; exact e1


theorem isContr_eq (X : Tm) : isContr X = sigma X (pi X.shift (pathC X.shift.shift (var 1) (var 0))) := rfl

/-- `idIsEquiv T f : isEquiv f` for `f` judgmentally the identity. -/
theorem idIsEquiv_typed (hS : SigClosed S) {Ψ Φ Γ T f l} (h : IsId S Ψ Φ Γ T f l) :
    HasTy0 S Ψ Φ Γ (idIsEquiv T f) (isEquiv T T f) := by
  have hE := isEquiv_typed hS h.ty h.ty h.fn
  rw [isEquiv_eq] at hE ⊢
  rw [idIsEquiv_eq]
  refine HasTy0.lam hE ?_
  have h1 := h.wk hS h.ty
  have hy : HasTy0 S Ψ Φ (T :: Γ) (var 0) T.shift := HasTy0.var (Wf0.cons h.ty) rfl
  have hF := fiber_typed hS h1.ty h1.ty h1.fn hy
  have hc := center_typed hS h1 hy
  have hpi : HasTy0 S Ψ Φ (T :: Γ) (pi (fiber T.shift T.shift f.shift (var 0))
      (pathC (fiber T.shift T.shift f.shift (var 0)).shift (center (var 0)).shift (var 0))) (univ l) :=
    HasTy0.pi hF (pathC_typed hS (HasTy0.wk hS hF hF) (HasTy0.wk hS hF hc) (HasTy0.var (Wf0.cons hF) rfl))
  have hC := isContr_typed hS hF
  rw [isContr_eq] at hC ⊢
  refine HasTy0.pair hC hc ?_
  rw [K_inst]
  exact HasTy0.lam hpi (contr_typed hS h1 hy)


theorem lineEquiv_eq (B : Tm) : lineEquiv B = pair ((lineFun B).dinst .one)
    (transp (isEquiv (B.dinst .zero).dshift B (lineFun B)) .zero
      (idIsEquiv (B.dinst .zero) ((lineFun B).dinst .zero))) := rfl

theorem equiv_eq (T A : Tm) : equiv T A = sigma (arrow T A) (isEquiv T.shift A.shift (var 0)) := rfl

/-- Transport along a line is an equivalence between its endpoints. -/
theorem lineEquiv_typed (hS : SigClosed S) {Ψ Φ Γ B l} (hB : HasTy0 S (Ψ + 1) Φ.shift Γ.dshift B (univ l)) :
    HasTy0 S Ψ Φ Γ (lineEquiv B) (equiv (B.dinst .zero) (B.dinst .one)) := by
  have hw0 := wf_unshift hS (wf_of_ty hB)
  have hs := scoped_of_wf hw0
  have hB0 := HasTy0.dsubst hS hB (r := .zero) trivial
  have hB1 := HasTy0.dsubst hS hB (r := .one) trivial
  have hB0d := HasTy0.dwk hS hB0
  obtain ⟨hlf, hid⟩ := lineFun_typed hS hB
  have hf r (hr : r.Scoped Ψ) : HasTy0 S Ψ Φ Γ ((lineFun B).dinst r) (arrow (B.dinst .zero) (B.dinst r)) := by
    have := HasTy0.dsubst hS hlf hr; rwa [arrow_dinst, dshift_dinst] at this
  have hE := isEquiv_typed hS hB0d hB hlf
  have hab : I.Entails (cof Φ .zero).shift .zero := ent_shift (ent_and_right Φ .zero)
  have hZs : (cof Φ .zero).shift.Scoped (Ψ + 1) := scoped_shift ⟨hs, trivial⟩
  have hbase := idIsEquiv_typed hS (Ψ := Ψ) (Φ := Φ) (Γ := Γ) ⟨hB0, hf .zero trivial, hid⟩
  have ht := HasTy0.transp hE (φ := .zero) trivial
    (EqTm0.absurd hab (HasTy0.restrict hZs (ent_shift (ent_and_left _ _)) hE)
      (HasTy0.restrict hZs (ent_shift (ent_and_left _ _)) (HasTy0.dwk hS (HasTy0.dsubst hS hE (r := .zero) trivial))))
    (by rw [isEquiv_dinst, dshift_dinst]; exact hbase)
  rw [isEquiv_dinst, dshift_dinst] at ht
  have hEq := equiv_typed hS hB0 hB1
  rw [equiv_eq] at hEq ⊢
  rw [lineEquiv_eq]
  exact HasTy0.pair hEq (hf .one trivial) (by rw [isEquiv_inst]; exact ht)


theorem equiv_inst1 (A T : Tm) : (equiv (var 0) A.shift).inst T = equiv T A := by
  simp only [equiv, isEquiv, isContr, fiber, pathC, arrow]; scalc
theorem equiv_inst2 (T A : Tm) : (equiv T.shift (var 0)).inst A = equiv T A := by
  simp only [equiv, isEquiv, isContr, fiber, pathC, arrow]; scalc

/-- Congruence of `equiv`, given a universe `univ l : univ l0`. -/
theorem equiv_cong (hS : SigClosed S) {Ψ Φ Γ T T' A A' l l0} (hU : HasTy0 S Ψ Φ Γ (univ l) (univ l0))
    (hT : HasTy0 S Ψ Φ Γ T (univ l)) (hT' : HasTy0 S Ψ Φ Γ T' (univ l))
    (hA : HasTy0 S Ψ Φ Γ A (univ l)) (hA' : HasTy0 S Ψ Φ Γ A' (univ l))
    (eT : EqTm0 S Ψ Φ Γ T T' (univ l)) (eA : EqTm0 S Ψ Φ Γ A A' (univ l)) :
    EqTm0 S Ψ Φ Γ (equiv T A) (equiv T' A') (univ l) := by
  have hv : HasTy0 S Ψ Φ (univ l :: Γ) (var 0) (univ l) := HasTy0.var (Wf0.cons hU) rfl
  have h1 : HasTy0 S Ψ Φ (univ l :: Γ) (equiv (var 0) A.shift) (univ l) :=
    equiv_typed hS hv (HasTy0.wk hS hU hA)
  have h2 : HasTy0 S Ψ Φ (univ l :: Γ) (equiv T'.shift (var 0)) (univ l) :=
    equiv_typed hS (HasTy0.wk hS hU hT') hv
  have e1 := HasTy0.inst_congr hS h1 hT hT' eT
  have e2 := HasTy0.inst_congr hS h2 hA hA' eA
  rw [equiv_inst1, equiv_inst1] at e1
  rw [equiv_inst2, equiv_inst2] at e2
  exact EqTm0.trans e1 e2

/-- The reversal of the line variable. -/
abbrev revI : Nat → I := sk (.neg (.var 0)) 1

theorem hcompU_eq (φ : I) (u u0 : Tm) :
    hcompU φ u u0 = glue u0 φ (u.dinst .one) (lineEquiv (u.dsubst revI)) := rfl

theorem rev_d0 (u : Tm) : (u.dsubst revI).dinst .zero = u.subst Tm.var (sk (.neg .zero) 0) := by
  ssub
theorem rev_d1 (u : Tm) : (u.dsubst revI).dinst .one = u.subst Tm.var (sk (.neg .one) 0) := by
  ssub

theorem hcompU_typed (hS : SigClosed S) {Ψ Φ Γ φ u u0 T l}
    (h : HasTy0 S Ψ Φ Γ (hcomp (univ l) φ u u0) T) : HasTy0 S Ψ Φ Γ (hcompU φ u u0) T := by
  obtain ⟨l0, ⟨hU, hφ, hu, hu0, hside⟩, ch⟩ := gen_hcomp h rfl
  refine ch.transport ?_
  rw [hcompU_eq]
  have hs := scoped_of_ty h
  have hX : (cof Φ φ).Scoped Ψ := ⟨hs, hφ⟩
  have hu' : HasTy0 S (Ψ + 1) (cof Φ φ).shift Γ.dshift u (univ l) := hu
  have hw1 := wf_of_ty hu'
  have hB : HasTy0 S (Ψ + 1) (cof Φ φ).shift Γ.dshift (u.dsubst revI) (univ l) := by
    have := HasTy0.isub hS (τ := revI) hu'
      (fun i hi => by rcases i with _ | i
                      · exact (show 0 < Ψ + 1 by omega)
                      · show i + 1 < Ψ + 1; omega)
      (ent_sk1 _ (ent_refl _))
      (by rw [ctxI_sk1]; exact hw1)
    rwa [ctxI_sk1] at this
  have hLE := lineEquiv_typed hS hB
  rw [rev_d0, rev_d1] at hLE
  have hw0 : Wf0 S Ψ (cof Φ φ) (ctxI (fun n => .var (n + 0)) Γ) := by
    rw [ctxI_add0]; exact wf_unshift hS hw1
  have hX0 : I.Entails (cof Φ φ) ((cof Φ φ).subst (fun n => .var (n + 0))) := by rw [I_add0]; exact ent_refl _
  have e0 := line_ieq hS hu' (k := 0) (Ψ' := Ψ) (r := .neg .zero) (r' := .one) hX0 trivial trivial (by omega)
    I_eq_neg_zero hw0
  have e1 := line_ieq hS hu' (k := 0) (Ψ' := Ψ) (r := .neg .one) (r' := .zero) hX0 trivial trivial (by omega)
    I_eq_neg_one hw0
  rw [ctxI_add0, sk_one0] at e0
  rw [ctxI_add0, sk_zero0] at e1
  have hT1 : HasTy0 S Ψ (cof Φ φ) Γ (u.dinst .one) (univ l) := HasTy0.dsubst hS hu' (r := .one) trivial
  have hUφ := HasTy0.restrict hX (ent_and_left _ _) hU
  have hu0φ := HasTy0.restrict hX (ent_and_left _ _) hu0
  have hd0 : HasTy0 S Ψ (cof Φ φ) Γ (u.subst Tm.var (sk (.neg .zero) 0)) (univ l) := by
    rw [← rev_d0]; exact HasTy0.dsubst hS hB (r := .zero) trivial
  have hd1 : HasTy0 S Ψ (cof Φ φ) Γ (u.subst Tm.var (sk (.neg .one) 0)) (univ l) := by
    rw [← rev_d1]; exact HasTy0.dsubst hS hB (r := .one) trivial
  have eq := equiv_cong hS hUφ hd0 hT1 hd1 hu0φ e0 (EqTm0.trans e1 hside)
  exact HasTy0.glue hu0 hφ hT1 (HasTy0.conv hLE eq)

end KubusCore.Meta
