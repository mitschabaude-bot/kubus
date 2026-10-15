import Model.Whnf.Valid2CompGlue

/-!
# Validity of `lineEquiv` and of the `hcomp` computation rule in the universe

The typing derivations of `KubusCore/Meta/KanU.lean`, with validity. Transport is only used at
types of a fixed level `l` (`KTAt S l`), so that the relatedness of `lineEquiv` at level `l` can feed a
level-stratified construction of composition in the universe.
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

/-- The Kan property of transport in all related lines of types of level `l`. -/
def KTAt (S : Sig) (l : ℕ) : Prop :=
  ∀ k (X X' : Tm), RT2 S (k + 1) X X' → HasTy S (k + 1) .one [] X (.univ l) → KanT2 S k X X'

theorem KTAt.of_all {S : Sig} (h : KTAll S) (l : ℕ) : KTAt S l := fun k X X' hX _ => h k X X' hX

variable {S : Sig} {k : ℕ}

variable (hW : WfSig S)
include hW

variable {Ψ : ℕ} {Φ : I} {Γ : Ctx}

/-! ### Paired formation rules -/

theorem VTy.pi' {A B : Tm} {l : ℕ} (hA : VTy S Ψ Φ Γ A (.univ l)) (hB : VTy S Ψ Φ (A :: Γ) B (.univ l)) :
    VTy S Ψ Φ Γ (.pi A B) (.univ l) := by
  have h := HasTy0.pi hA.ty hB.ty
  exact ⟨h, valid_pi hW hA.v hB.v h h (.refl h)⟩

theorem VTy.sigma' {A B : Tm} {l : ℕ} (hA : VTy S Ψ Φ Γ A (.univ l)) (hB : VTy S Ψ Φ (A :: Γ) B (.univ l)) :
    VTy S Ψ Φ Γ (.sigma A B) (.univ l) := by
  have h := HasTy0.sigma hA.ty hB.ty
  exact ⟨h, valid_sigma hW hA.v hB.v h h (.refl h)⟩

theorem VTy.path' {L a b : Tm} {l : ℕ} (hL : VTy S (Ψ + 1) Φ.shift Γ.dshift L (.univ l))
    (ha : VTy S Ψ Φ Γ a (L.dinst .zero)) (hb : VTy S Ψ Φ Γ b (L.dinst .one)) :
    VTy S Ψ Φ Γ (.path L a b) (.univ l) := by
  have h := HasTy0.path hL.ty ha.ty hb.ty
  exact ⟨h, valid_path hW hL.v ha.v hb.v h h (.refl h)⟩

theorem VEq.piBeta' {A b a T : Tm} (h : VTy S Ψ Φ Γ (.app (.lam A b) a) T) :
    VEq S Ψ Φ Γ (.app (.lam A b) a) (b.inst a) T := by
  have e := EqTm0.piBeta h.ty
  exact ⟨e, valid_piBeta hW h.v h.ty (presup hW e).2⟩

theorem VTy.transpL {A a : Tm} {φ : I} {l : ℕ} (hKT : KTAt S l)
    (hA : VTy S (Ψ + 1) Φ.shift Γ.dshift A (.univ l)) (hφ : φ.Scoped Ψ)
    (hc : VEq S (Ψ + 1) (cof Φ φ).shift Γ.dshift A (A.dinst .zero).dshift (.univ l))
    (ha : VTy S Ψ Φ Γ a (A.dinst .zero)) : VTy S Ψ Φ Γ (.transp A φ a) (A.dinst .one) :=
  VTy.transp' hW (fun k c => hKT k _ _ (hA.v.ty hW (c.up hW)) ((c.up hW).ty hW hA.ty)) hA hφ hc ha

/-! ### Types of equivalences -/

theorem VTy.var0' {X : Tm} {l : ℕ} (hX : VTy S Ψ Φ Γ X (.univ l)) : VTy S Ψ Φ (X :: Γ) (.var 0) X.shift :=
  VTy.var' hW (Wf0.cons hX.ty) rfl

theorem VTy.pathC' {A a b : Tm} {l : ℕ} (hA : VTy S Ψ Φ Γ A (.univ l)) (ha : VTy S Ψ Φ Γ a A)
    (hb : VTy S Ψ Φ Γ b A) : VTy S Ψ Φ Γ (Tm.pathC A a b) (.univ l) := by
  have hAd := VTy.dwk' hW hA
  exact VTy.path' hW hAd (by rw [dshift_dinst]; exact ha) (by rw [dshift_dinst]; exact hb)

theorem VTy.isContr' {X : Tm} {l : ℕ} (hX : VTy S Ψ Φ Γ X (.univ l)) :
    VTy S Ψ Φ Γ (Tm.isContr X) (.univ l) := by
  have hX1 := VTy.wk' hW hX.ty hX
  have hX2 := VTy.wk' hW hX1.ty hX1
  have hv1 : VTy S Ψ Φ (X.shift :: X :: Γ) (.var 1) X.shift.shift := VTy.var' hW (Wf0.cons hX1.ty) rfl
  have hv0 : VTy S Ψ Φ (X.shift :: X :: Γ) (.var 0) X.shift.shift := VTy.var' hW (Wf0.cons hX1.ty) rfl
  exact VTy.sigma' hW hX (VTy.pi' hW hX1 (VTy.pathC' hW hX2 hv1 hv0))

theorem VTy.fiber' {T A f y : Tm} {l : ℕ} (hT : VTy S Ψ Φ Γ T (.univ l)) (hA : VTy S Ψ Φ Γ A (.univ l))
    (hf : VTy S Ψ Φ Γ f (Tm.arrow T A)) (hy : VTy S Ψ Φ Γ y A) :
    VTy S Ψ Φ Γ (Tm.fiber T A f y) (.univ l) := by
  have hA1 := VTy.wk' hW hT.ty hA
  have hf1 := VTy.wk' hW hT.ty hf
  rw [arrow_shift] at hf1
  have happ := VTy.app' hW hf1 (VTy.var0' hW hT)
  rw [shift_inst] at happ
  exact VTy.sigma' hW hT (VTy.pathC' hW hA1 happ (VTy.wk' hW hT.ty hy))

theorem VTy.isEquiv' {T A f : Tm} {l : ℕ} (hT : VTy S Ψ Φ Γ T (.univ l)) (hA : VTy S Ψ Φ Γ A (.univ l))
    (hf : VTy S Ψ Φ Γ f (Tm.arrow T A)) : VTy S Ψ Φ Γ (Tm.isEquiv T A f) (.univ l) := by
  have hT1 := VTy.wk' hW hA.ty hT
  have hA1 := VTy.wk' hW hA.ty hA
  have hf1 := VTy.wk' hW hA.ty hf
  rw [arrow_shift] at hf1
  exact VTy.pi' hW hA (VTy.isContr' hW (VTy.fiber' hW hT1 hA1 hf1 (VTy.var0' hW hA)))

theorem VTy.arrow' {T A : Tm} {l : ℕ} (hT : VTy S Ψ Φ Γ T (.univ l)) (hA : VTy S Ψ Φ Γ A (.univ l)) :
    VTy S Ψ Φ Γ (Tm.arrow T A) (.univ l) := VTy.pi' hW hT (VTy.wk' hW hT.ty hA)

theorem VTy.equiv' {T A : Tm} {l : ℕ} (hT : VTy S Ψ Φ Γ T (.univ l)) (hA : VTy S Ψ Φ Γ A (.univ l)) :
    VTy S Ψ Φ Γ (Tm.equiv T A) (.univ l) := by
  have hTA := VTy.arrow' hW hT hA
  have hv := VTy.var0' hW hTA
  rw [arrow_shift] at hv
  exact VTy.sigma' hW hTA (VTy.isEquiv' hW (VTy.wk' hW hTA.ty hT) (VTy.wk' hW hTA.ty hA) hv)

/-! ### The transport filler with a constant cofibration -/

theorem VTy.tfill' {C a : Tm} {l : ℕ} (hKT : KTAt S l) (hC : VTy S (Ψ + 1) Φ.shift Γ.dshift C (.univ l))
    (ha : VTy S Ψ Φ Γ a (C.dinst .zero)) :
    VTy S (Ψ + 1) Φ.shift Γ.dshift (KubusCore.Meta.tfill C a) C ∧ VEq S Ψ Φ Γ ((KubusCore.Meta.tfill C a).dinst .zero) a (C.dinst .zero) := by
  have hS := sigClosed_of_wfSig hW
  have hw0 := wf_unshift hS (wf_of_ty hC.ty)
  have hs := scoped_of_wf hw0
  have hv0 : (I.var 0).Scoped (Ψ + 1) := show 0 < Ψ + 1 by omega
  have hv1 : (I.var 1).Scoped (Ψ + 1 + 1) := show 1 < Ψ + 1 + 1 by omega
  have hv0' : (I.var 0).Scoped (Ψ + 1 + 1) := show 0 < Ψ + 1 + 1 by omega
  have hL := VTy.bind2' hW (X := Φ.shift.shift) (r := .and (.var 1) (.var 0)) ⟨hv1, hv0'⟩ hs (ent_refl _)
    (hw0.dwk2 hS) hC
  rw [univ_dsubst] at hL
  let Y : I := (cof Φ.shift (.neg (.var 0))).shift
  have hYs : Y.Scoped (Ψ + 1 + 1) := KubusCore.I.scoped_shift ⟨KubusCore.I.scoped_shift hs, hv0⟩
  have hYΦ : I.Entails Y Φ.shift.shift := ent_shift (ent_and_left _ _)
  have hY1 : I.Entails Y (I.lit 1 false) := ent_shift (ent_and_right _ (.neg (.var 0)))
  have hYΦ2 : I.Entails Y (Φ.subst (fun n => .var (n + 2))) := by rw [I_add2]; exact hYΦ
  have hwY : Wf0 S (Ψ + 2) Y (Ctx.dren 2 Γ) := by
    rw [Ctx.dren_two]; exact (hw0.dwk2 hS).restrict hYs hYΦ
  have hconst : VEq S (Ψ + 1 + 1) Y Γ.dshift.dshift
      (C.dsubst (Tm.bind2 (.and (.var 1) (.var 0))))
      ((C.dsubst (Tm.bind2 (.and (.var 1) (.var 0)))).dinst .zero).dshift (.univ l) := by
    have hLY := VTy.restrict' hW hYs hYΦ hL
    have e1 := VEq.faceU' hW (i := 1) (d := false) hv1 hY1 hLY
    rw [tf_L1] at e1
    have e2 := VTy.lineIeq hW hC (k := 2) (r := .and .zero (.var 0)) (r' := .zero) hYΦ2
      ⟨trivial, hv0'⟩ trivial (I_eq_and_zero _) hwY
    rw [Ctx.dren_two] at e2
    have hL0 := VTy.restrict' hW hYs hYΦ
      (VTy.dwk' hW (VTy.dsubst' hW (Φ := Φ.shift) (Γ := Γ.dshift) .zero trivial hL))
    rw [tf_L0s] at hL0
    have e3 := VEq.faceU' hW (i := 1) (d := false) hv1 hY1 hL0
    rw [tf_L0s1] at e3
    have e4 := VTy.lineIeq hW hC (k := 2) (r := .and .zero .zero) (r' := .zero) hYΦ2
      ⟨trivial, trivial⟩ trivial (I_eq_and_zero _) hwY
    rw [Ctx.dren_two] at e4
    rw [tf_L0s]
    exact VEq.trans' hW e1 (VEq.trans' hW e2 (VEq.symm' hW (VEq.trans' hW e3 e4)))
  have hwX : Wf0 S (Ψ + 1) Φ.shift (Ctx.dren 1 Γ) := wf_of_ty hC.ty
  have ha' : VTy S (Ψ + 1) Φ.shift Γ.dshift a.dshift ((C.dsubst (Tm.bind2 (.and (.var 1) (.var 0)))).dinst .zero) := by
    rw [tf_L0]
    have e := VTy.lineIeq hW hC (k := 1) (r := .zero) (r' := .and (.var 0) .zero) (ent_refl _) trivial
      ⟨hv0, trivial⟩ (I_eq_symm (I_eq_and_zero_r _)) hwX
    rw [sk_zero1] at e
    exact VTy.conv' hW (VTy.dwk' hW ha) e
  have ht0 := VTy.transpL hW hKT hL (show (I.neg (.var 0)).Scoped (Ψ + 1) from hv0) hconst ha'
  have eC : VEq S (Ψ + 1) Φ.shift Γ.dshift ((C.dsubst (Tm.bind2 (.and (.var 1) (.var 0)))).dinst .one) C (.univ l) := by
    have e := VTy.lineIeq hW hC (k := 1) (r := .and (.var 0) .one) (r' := .var 0) (ent_refl _)
      ⟨hv0, trivial⟩ hv0 (I_eq_and_one_r _) hwX
    rw [sk_var1] at e
    rw [tf_L1']; exact e
  refine ⟨VTy.conv' hW ht0 eC, ?_⟩
  have h0 := VTy.dsubst' hW .zero trivial ht0
  have eC0 := VEq.dsubst' hW .zero trivial eC
  have hf : VEq S Ψ Φ Γ ((KubusCore.Meta.tfill C a).dinst .zero) (a.dshift.dinst .zero) _ :=
    VEq.transpFace' hW (φ := (I.neg (.var 0)).subst (I.inst0 .zero)) (ent_negzero Φ) h0
  rw [dshift_dinst] at hf
  exact VEq.conv' hW hf eC0

theorem VTy.lineFun' {B : Tm} {l : ℕ} (hKT : KTAt S l) (hB : VTy S (Ψ + 1) Φ.shift Γ.dshift B (.univ l)) :
    VTy S (Ψ + 1) Φ.shift Γ.dshift (Tm.lineFun B) (Tm.arrow (B.dinst .zero).dshift B) ∧
      VEq S Ψ Φ Γ ((Tm.lineFun B).dinst .zero) (.lam (B.dinst .zero) (.var 0))
        (Tm.arrow (B.dinst .zero) (B.dinst .zero)) := by
  have hB0 := VTy.dsubst' hW .zero trivial hB
  have hB0d := VTy.dwk' hW hB0
  have hC : VTy S (Ψ + 1) Φ.shift (Ctx.dshift (B.dinst .zero :: Γ)) B.shift (.univ l) := VTy.wk' hW hB0d.ty hB
  have ha : VTy S Ψ Φ (B.dinst .zero :: Γ) (.var 0) (B.shift.dinst .zero) := by
    rw [shift_dinst_comm]; exact VTy.var0' hW hB0
  obtain ⟨ht, he⟩ := VTy.tfill' hW hKT hC ha
  have hpi : VTy S (Ψ + 1) Φ.shift Γ.dshift (.pi (B.dinst .zero).dshift B.shift) (.univ l) :=
    VTy.pi' hW hB0d (VTy.wk' hW hB0d.ty hB)
  refine ⟨VTy.lam' hW hpi ht, ?_⟩
  rw [lineFun_eq, lam_dinst, dshift_dinst]
  rw [shift_dinst_comm] at he
  exact VEq.lam' hW (VTy.pi' hW hB0 (VTy.wk' hW hB0.ty hB0)) he

/-! ### The identity is an equivalence -/

/-- `f : T → T` is judgmentally the identity (typed and valid). -/
structure VIsId (S : Sig) (Ψ : ℕ) (Φ : I) (Γ : Ctx) (T f : Tm) (l : ℕ) : Prop where
  ty : VTy S Ψ Φ Γ T (.univ l)
  fn : VTy S Ψ Φ Γ f (Tm.arrow T T)
  id : VEq S Ψ Φ Γ f (.lam T (.var 0)) (Tm.arrow T T)

theorem VIsId.wk {T f B : Tm} {l l' : ℕ} (h : VIsId S Ψ Φ Γ T f l) (hB : HasTy0 S Ψ Φ Γ B (.univ l')) :
    VIsId S Ψ Φ (B :: Γ) T.shift f.shift l where
  ty := VTy.wk' hW hB h.ty
  fn := by have := VTy.wk' hW hB h.fn; rwa [arrow_shift] at this
  id := by have := VEq.wk' hW hB h.id; rwa [lamid_shift, arrow_shift] at this

theorem VIsId.dwk {T f : Tm} {l : ℕ} (h : VIsId S Ψ Φ Γ T f l) :
    VIsId S (Ψ + 1) Φ.shift Γ.dshift T.dshift f.dshift l where
  ty := VTy.dwk' hW h.ty
  fn := by have := VTy.dwk' hW h.fn; rwa [arrow_dshift] at this
  id := by have := VEq.dwk' hW h.id; rwa [lamid_dshift, arrow_dshift] at this

theorem VIsId.app_ty {T f x : Tm} {l : ℕ} (h : VIsId S Ψ Φ Γ T f l) (hx : VTy S Ψ Φ Γ x T) :
    VTy S Ψ Φ Γ (.app f x) T := by
  have := VTy.app' hW h.fn hx; rwa [shift_inst] at this

theorem VIsId.app_eq {T f x : Tm} {l : ℕ} (h : VIsId S Ψ Φ Γ T f l) (hx : VTy S Ψ Φ Γ x T) :
    VEq S Ψ Φ Γ (.app f x) x T := by
  have hlam : VTy S Ψ Φ Γ (.lam T (.var 0)) (Tm.arrow T T) :=
    VTy.lam' hW (VTy.pi' hW h.ty (VTy.wk' hW h.ty.ty h.ty)) (VTy.var0' hW h.ty)
  have e1 := VEq.app' hW h.id (VEq.refl' hx)
  have e2 := VEq.piBeta' hW (VTy.app' hW hlam hx)
  rw [shift_inst] at e1 e2
  exact VEq.trans' hW e1 e2

theorem VTy.pappC' {p A a b : Tm} {r : I} (hp : VTy S Ψ Φ Γ p (Tm.pathC A a b)) (hr : r.Scoped Ψ) :
    VTy S Ψ Φ Γ (.papp p r) A := by
  have := VTy.papp' hW hp hr; rwa [dshift_dinst] at this

theorem VEq.pappC' {p A a b : Tm} {r r' : I} (hp : VTy S Ψ Φ Γ p (Tm.pathC A a b)) (hr : r.Scoped Ψ)
    (hr' : r'.Scoped Ψ) (he : I.Eq r r') : VEq S Ψ Φ Γ (.papp p r) (.papp p r') A := by
  have := VEq.papp' hW (VEq.refl' hp) hr hr' he; rwa [dshift_dinst] at this

theorem VEq.pathCOne' {p A a b : Tm} (hp : VTy S Ψ Φ Γ p (Tm.pathC A a b)) :
    VEq S Ψ Φ Γ (.papp p .one) b A := by
  have := VEq.pathOne' hW hp; rwa [dshift_dinst] at this

theorem VEq.pathCZero' {p A a b : Tm} (hp : VTy S Ψ Φ Γ p (Tm.pathC A a b)) :
    VEq S Ψ Φ Γ (.papp p .zero) a A := by
  have := VEq.pathZero' hW hp; rwa [dshift_dinst] at this

theorem VTy.plamConst' {A a b : Tm} {l : ℕ} (hA : VTy S Ψ Φ Γ A (.univ l))
    (ha : VTy S Ψ Φ Γ a A) (hb : VTy S Ψ Φ Γ b A) (he : VEq S Ψ Φ Γ b a A) :
    VTy S Ψ Φ Γ (.plam b.dshift) (Tm.pathC A a b) :=
  VTy.plam' hW (VTy.pathC' hW hA ha hb) (VTy.dwk' hW hb)
    (by rw [dshift_dinst, dshift_dinst]; exact he) (by rw [dshift_dinst, dshift_dinst]; exact VEq.refl' hb)

theorem VTy.Q' {T f y : Tm} {l : ℕ} (h : VIsId S Ψ Φ Γ T f l) (hy : VTy S Ψ Φ Γ y T) :
    VTy S Ψ Φ (T :: Γ) (Tm.pathC T.shift (.app f.shift (.var 0)) y.shift) (.univ l) := by
  have h1 := h.wk hW h.ty.ty
  exact VTy.pathC' hW h1.ty (h1.app_ty hW (VTy.var0' hW h.ty)) (VTy.wk' hW h.ty.ty hy)

theorem VTy.center' {T f y : Tm} {l : ℕ} (h : VIsId S Ψ Φ Γ T f l) (hy : VTy S Ψ Φ Γ y T) :
    VTy S Ψ Φ Γ (KubusCore.Meta.center y) (Tm.fiber T T f y) :=
  VTy.pair' hW (VTy.fiber' hW h.ty h.ty h.fn hy) hy (by
    rw [P_inst]; exact VTy.plamConst' hW h.ty (h.app_ty hW hy) hy (VEq.symm' hW (h.app_eq hW hy)))

theorem VTy.contr' {T f y : Tm} {l : ℕ} (h : VIsId S Ψ Φ Γ T f l) (hy : VTy S Ψ Φ Γ y T) :
    VTy S Ψ Φ (Tm.fiber T T f y :: Γ)
      (.plam (.pair (.papp (.snd (.var 0)) (.neg (.var 0)))
        (.plam (.papp (.snd (.var 0)) (.or (.neg (.var 1)) (.var 0))))))
      (Tm.pathC (Tm.fiber T T f y).shift (KubusCore.Meta.center y).shift (.var 0)) := by
  have hF := VTy.fiber' hW h.ty h.ty h.fn hy
  have h2 := h.wk hW hF.ty
  have hy2 := VTy.wk' hW hF.ty hy
  have hF2 := VTy.fiber' hW h2.ty h2.ty h2.fn hy2
  have hw : VTy S Ψ Φ (Tm.fiber T T f y :: Γ) (.var 0) (Tm.fiber T.shift T.shift f.shift y.shift) := by
    have := VTy.var0' hW hF; rwa [fiber_shift] at this
  have hfst := VTy.fst' hW hw
  have hp : VTy S Ψ Φ (Tm.fiber T T f y :: Γ) (.snd (.var 0))
      (Tm.pathC T.shift (.app f.shift (.fst (.var 0))) y.shift) := by
    have := VTy.snd' hW hw; rwa [P_inst] at this
  have h2d := h2.dwk hW
  have hy2d := VTy.dwk' hW hy2
  have hp1 : VTy S (Ψ + 1) Φ.shift (Ctx.dshift (Tm.fiber T T f y :: Γ)) (.snd (.var 0))
      (Tm.pathC T.shift.dshift (Tm.app f.shift (.fst (.var 0))).dshift y.shift.dshift) := by
    have := VTy.dwk' hW hp; rw [pathC_dshift] at this; exact this
  have hp2 : VTy S (Ψ + 1 + 1) Φ.shift.shift (Ctx.dshift (Ctx.dshift (Tm.fiber T T f y :: Γ))) (.snd (.var 0))
      (Tm.pathC T.shift.dshift.dshift (Tm.app f.shift (.fst (.var 0))).dshift.dshift y.shift.dshift.dshift) := by
    have := VTy.dwk' hW hp1; rw [pathC_dshift] at this; exact this
  have hv0 : (I.var 0).Scoped (Ψ + 1) := show 0 < Ψ + 1 by omega
  have hv0' : (I.var 0).Scoped (Ψ + 1 + 1) := show 0 < Ψ + 1 + 1 by omega
  have hv1' : (I.var 1).Scoped (Ψ + 1 + 1) := show 1 < Ψ + 1 + 1 by omega
  have ha := VTy.pappC' hW hp1 (r := .neg (.var 0)) hv0
  -- the inner path, from `f (p(~i))` to `y`
  have hinner : VTy S (Ψ + 1) Φ.shift (Ctx.dshift (Tm.fiber T T f y :: Γ))
      (.plam (.papp (.snd (.var 0)) (.or (.neg (.var 1)) (.var 0))))
      (Tm.pathC T.shift.dshift (.app f.shift.dshift (.papp (.snd (.var 0)) (.neg (.var 0)))) y.shift.dshift) := by
    refine VTy.plam' hW (VTy.pathC' hW h2d.ty (h2d.app_ty hW ha) hy2d)
      (VTy.pappC' hW hp2 (r := .or (.neg (.var 1)) (.var 0)) ⟨hv1', hv0'⟩) ?_ ?_
    · show VEq _ _ _ _ (.papp (.snd (.var 0)) (.or (.neg (.var 0)) .zero)) _ _
      rw [dshift_dinst]
      exact VEq.trans' hW (VEq.pappC' hW hp1 (r' := .neg (.var 0)) ⟨hv0, trivial⟩ hv0 (I_eq_or_zero_r _))
        (VEq.symm' hW (h2d.app_eq hW ha))
    · show VEq _ _ _ _ (.papp (.snd (.var 0)) (.or (.neg (.var 0)) .one)) _ _
      rw [dshift_dinst]
      exact VEq.trans' hW (VEq.pappC' hW hp1 (r' := .one) ⟨hv0, trivial⟩ trivial (I_eq_or_one_r _))
        (VEq.pathCOne' hW hp1)
  have hbody : VTy S (Ψ + 1) Φ.shift (Ctx.dshift (Tm.fiber T T f y :: Γ))
      (.pair (.papp (.snd (.var 0)) (.neg (.var 0))) (.plam (.papp (.snd (.var 0)) (.or (.neg (.var 1)) (.var 0)))))
      (Tm.fiber T.shift.dshift T.shift.dshift f.shift.dshift y.shift.dshift) :=
    VTy.pair' hW (VTy.fiber' hW h2d.ty h2d.ty h2d.fn hy2d) ha (by rw [P_inst]; exact hinner)
  have hQ := VTy.Q' hW h2 hy2
  -- endpoint `i = 0`: the centre
  have ha0 := VTy.pappC' hW hp (r := .neg .zero) trivial
  have ea0 : VEq S Ψ Φ (Tm.fiber T T f y :: Γ) (.papp (.snd (.var 0)) (.neg .zero)) y.shift T.shift :=
    VEq.trans' hW (VEq.pappC' hW hp (r' := .one) trivial trivial I_eq_neg_zero) (VEq.pathCOne' hW hp)
  have hl0 : VTy S Ψ Φ (Tm.fiber T T f y :: Γ) (.plam (.papp (.snd (.var 0)) (.or (.neg .zero) (.var 0))))
      (Tm.pathC T.shift (.app f.shift (.papp (.snd (.var 0)) (.neg .zero))) y.shift) := by
    have := VTy.dsubst' hW .zero trivial hinner
    rw [pathC_dinst, dshift_dinst, dshift_dinst, app_dshift_dinst] at this; exact this
  have hpath0 := VTy.pathC' hW h2.ty (h2.app_ty hW ha0) hy2
  have hr0 : VTy S Ψ Φ (Tm.fiber T T f y :: Γ) (.plam y.shift.dshift)
      (Tm.pathC T.shift (.app f.shift (.papp (.snd (.var 0)) (.neg .zero))) y.shift) :=
    VTy.plamConst' hW h2.ty (h2.app_ty hW ha0) hy2 (VEq.symm' hW (VEq.trans' hW (h2.app_eq hW ha0) ea0))
  have e0 : VEq S Ψ Φ (Tm.fiber T T f y :: Γ)
      (.pair (.papp (.snd (.var 0)) (.neg .zero)) (.plam (.papp (.snd (.var 0)) (.or (.neg .zero) (.var 0)))))
      (KubusCore.Meta.center y.shift) (Tm.fiber T.shift T.shift f.shift y.shift) := by
    refine VEq.pair' hW hF2 ea0 ?_
    rw [P_inst]
    refine VEq.plam' hW hpath0 hl0 hr0.ty ?_
    exact VEq.trans' hW (VEq.pappC' hW hp1 (r' := .one) ⟨trivial, hv0⟩ trivial (I_eq_or_negzero _))
      (VEq.pathCOne' hW hp1)
  -- endpoint `i = 1`: the given point of the fibre
  have ha1 := VTy.pappC' hW hp (r := .neg .one) trivial
  have ea1 : VEq S Ψ Φ (Tm.fiber T T f y :: Γ) (.papp (.snd (.var 0)) (.neg .one)) (.fst (.var 0)) T.shift :=
    VEq.trans' hW (VEq.pappC' hW hp (r' := .zero) trivial trivial I_eq_neg_one)
      (VEq.trans' hW (VEq.pathCZero' hW hp) (h2.app_eq hW hfst))
  have eQ := VTy.inst_congr' hW h2.ty hQ ea1
  rw [P_inst, P_inst] at eQ
  have hl1 : VTy S Ψ Φ (Tm.fiber T T f y :: Γ) (.plam (.papp (.snd (.var 0)) (.or (.neg .one) (.var 0))))
      (Tm.pathC T.shift (.app f.shift (.fst (.var 0))) y.shift) := by
    have := VTy.dsubst' hW .one trivial hinner
    rw [pathC_dinst, dshift_dinst, dshift_dinst, app_dshift_dinst] at this; exact VTy.conv' hW this eQ
  have hr1 : VTy S Ψ Φ (Tm.fiber T T f y :: Γ) (.plam (.papp (Tm.snd (.var 0)).dshift (.var 0)))
      (Tm.pathC T.shift (.app f.shift (.fst (.var 0))) y.shift) := by
    refine VTy.plam' hW (VTy.pathC' hW h2.ty (h2.app_ty hW hfst) hy2) (VTy.pappC' hW hp1 hv0) ?_ ?_
    · show VEq _ _ _ _ (.papp (.snd (.var 0)) .zero) _ _; rw [dshift_dinst]; exact VEq.pathCZero' hW hp
    · show VEq _ _ _ _ (.papp (.snd (.var 0)) .one) _ _; rw [dshift_dinst]; exact VEq.pathCOne' hW hp
  have eb1 : VEq S Ψ Φ (Tm.fiber T T f y :: Γ) (.plam (.papp (.snd (.var 0)) (.or (.neg .one) (.var 0))))
      (.snd (.var 0)) (Tm.pathC T.shift (.app f.shift (.fst (.var 0))) y.shift) :=
    VEq.trans' hW (VEq.plam' hW (VTy.pathC' hW h2.ty (h2.app_ty hW hfst) hy2) hl1 hr1.ty
      (VEq.pappC' hW hp1 (r' := .var 0) ⟨trivial, hv0⟩ hv0 (I_eq_or_negone _)))
      (VEq.symm' hW (VEq.pathEta' hW hp))
  have e1 : VEq S Ψ Φ (Tm.fiber T T f y :: Γ)
      (.pair (.papp (.snd (.var 0)) (.neg .one)) (.plam (.papp (.snd (.var 0)) (.or (.neg .one) (.var 0)))))
      (.var 0) (Tm.fiber T.shift T.shift f.shift y.shift) := by
    refine VEq.trans' hW ?_ (VEq.symm' hW (VEq.sigmaEta' hW hw))
    refine VEq.pair' hW hF2 ea1 ?_
    rw [P_inst]; exact VEq.conv' hW eb1 (VEq.symm' hW eQ)
  rw [fiber_shift, center_shift]
  refine VTy.plam' hW (VTy.pathC' hW hF2 (VTy.center' hW h2 hy2) hw) (by rw [fiber_dshift]; exact hbody) ?_ ?_
  · rw [dshift_dinst]; exact e0
  · rw [dshift_dinst]; exact e1

theorem VTy.idIsEquiv' {T f : Tm} {l : ℕ} (h : VIsId S Ψ Φ Γ T f l) :
    VTy S Ψ Φ Γ (Tm.idIsEquiv T f) (Tm.isEquiv T T f) := by
  have hE := VTy.isEquiv' hW h.ty h.ty h.fn
  rw [isEquiv_eq] at hE ⊢
  rw [idIsEquiv_eq]
  refine VTy.lam' hW hE ?_
  have h1 := h.wk hW h.ty.ty
  have hy : VTy S Ψ Φ (T :: Γ) (.var 0) T.shift := VTy.var0' hW h.ty
  have hF := VTy.fiber' hW h1.ty h1.ty h1.fn hy
  have hc := VTy.center' hW h1 hy
  have hpi : VTy S Ψ Φ (T :: Γ) (.pi (Tm.fiber T.shift T.shift f.shift (.var 0))
      (Tm.pathC (Tm.fiber T.shift T.shift f.shift (.var 0)).shift (KubusCore.Meta.center (.var 0)).shift (.var 0)))
      (.univ l) :=
    VTy.pi' hW hF (VTy.pathC' hW (VTy.wk' hW hF.ty hF) (VTy.wk' hW hF.ty hc) (VTy.var0' hW hF))
  have hC := VTy.isContr' hW hF
  rw [isContr_eq] at hC ⊢
  refine VTy.pair' hW hC hc ?_
  rw [K_inst]
  exact VTy.lam' hW hpi (VTy.contr' hW h1 hy)

/-- Transport along a line of types of level `l` is an equivalence between its endpoints. -/
theorem VTy.lineEquiv' {B : Tm} {l : ℕ} (hKT : KTAt S l) (hB : VTy S (Ψ + 1) Φ.shift Γ.dshift B (.univ l)) :
    VTy S Ψ Φ Γ (Tm.lineEquiv B) (Tm.equiv (B.dinst .zero) (B.dinst .one)) := by
  have hS := sigClosed_of_wfSig hW
  have hw0 := wf_unshift hS (wf_of_ty hB.ty)
  have hs := scoped_of_wf hw0
  have hB0 := VTy.dsubst' hW .zero trivial hB
  have hB1 := VTy.dsubst' hW .one trivial hB
  have hB0d := VTy.dwk' hW hB0
  obtain ⟨hlf, hid⟩ := VTy.lineFun' hW hKT hB
  have hf : ∀ r : I, r.Scoped Ψ → VTy S Ψ Φ Γ ((Tm.lineFun B).dinst r) (Tm.arrow (B.dinst .zero) (B.dinst r)) := by
    intro r hr
    have := VTy.dsubst' hW r hr hlf; rwa [arrow_dinst, dshift_dinst] at this
  have hE := VTy.isEquiv' hW hB0d hB hlf
  have hab : I.Entails (cof Φ .zero).shift .zero := ent_shift (ent_and_right Φ .zero)
  have hZs : (cof Φ .zero).shift.Scoped (Ψ + 1) := KubusCore.I.scoped_shift ⟨hs, trivial⟩
  have hbase := VTy.idIsEquiv' hW (Ψ := Ψ) (Φ := Φ) (Γ := Γ) ⟨hB0, hf .zero trivial, hid⟩
  have ht := VTy.transpL hW hKT hE (φ := .zero) trivial
    (VEq.absurd' hW hab (VTy.restrict' hW hZs (ent_shift (ent_and_left _ _)) hE).ty
      (VTy.restrict' hW hZs (ent_shift (ent_and_left _ _)) (VTy.dwk' hW (VTy.dsubst' hW .zero trivial hE))).ty)
    (by rw [isEquiv_dinst, dshift_dinst]; exact hbase)
  rw [isEquiv_dinst, dshift_dinst] at ht
  have hEq := VTy.equiv' hW hB0 hB1
  rw [equiv_eq] at hEq ⊢
  rw [lineEquiv_eq]
  exact VTy.pair' hW hEq (hf .one trivial) (by rw [isEquiv_inst]; exact ht)

/-- Congruence of `equiv`, given a universe `univ l : univ l0`. -/
theorem VEq.equivCong' {T T' A A' : Tm} {l l0 : ℕ} (hU : VTy S Ψ Φ Γ (.univ l) (.univ l0))
    (hT' : VTy S Ψ Φ Γ T' (.univ l)) (hA : VTy S Ψ Φ Γ A (.univ l))
    (eT : VEq S Ψ Φ Γ T T' (.univ l)) (eA : VEq S Ψ Φ Γ A A' (.univ l)) :
    VEq S Ψ Φ Γ (Tm.equiv T A) (Tm.equiv T' A') (.univ l) := by
  have hv : VTy S Ψ Φ (.univ l :: Γ) (.var 0) (.univ l) := VTy.var0' hW hU
  have h1 : VTy S Ψ Φ (.univ l :: Γ) (Tm.equiv (.var 0) A.shift) (.univ l) :=
    VTy.equiv' hW hv (VTy.wk' hW hU.ty hA)
  have h2 : VTy S Ψ Φ (.univ l :: Γ) (Tm.equiv T'.shift (.var 0)) (.univ l) :=
    VTy.equiv' hW (VTy.wk' hW hU.ty hT') hv
  have e1 := VTy.inst_congr' hW hU h1 eT
  have e2 := VTy.inst_congr' hW hU h2 eA
  rw [equiv_inst1, equiv_inst1] at e1
  rw [equiv_inst2, equiv_inst2] at e2
  exact VEq.trans' hW e1 e2

/-! ### `hcomp` in the universe -/

/-- The contractum of `hcompU`, typed and valid, using transport at types of level `l` only. -/
theorem VTy.hcompU' {u u0 : Tm} {φ : I} {l l0 : ℕ} (hKT : KTAt S l) (hU : VTy S Ψ Φ Γ (.univ l) (.univ l0))
    (hφ : φ.Scoped Ψ) (hu : VTy S (Ψ + 1) (cof Φ φ).shift Γ.dshift u (.univ l))
    (hu0 : VTy S Ψ Φ Γ u0 (.univ l)) (hside : VEq S Ψ (cof Φ φ) Γ (u.dinst .zero) u0 (.univ l)) :
    VTy S Ψ Φ Γ (Tm.hcompU φ u u0) (.univ l) := by
  have hS := sigClosed_of_wfSig hW
  have hs := scoped_of_ty hU.ty
  have hX : (cof Φ φ).Scoped Ψ := ⟨hs, hφ⟩
  rw [hcompU_eq]
  have hw1 := wf_of_ty hu.ty
  have hB : VTy S (Ψ + 1) (cof Φ φ).shift Γ.dshift (u.dsubst revI) (.univ l) := by
    have := VTy.isubL hW (n := 1) (m := 1) (Ψ0 := Ψ) (Φs := (cof Φ φ).shift) (Γ0 := Γ) revI
      (fun i hi => by rcases Nat.lt_one_iff.1 hi with rfl; exact (show 0 < Ψ + 1 by omega))
      (fun i => rfl) (KubusCore.I.scoped_shift hX) (ent_sk1 _ (ent_refl _)) hw1 hu
    exact this
  have hLE := VTy.lineEquiv' hW hKT hB
  rw [rev_d0, rev_d1] at hLE
  have hw0 : Wf0 S (Ψ + 0) (cof Φ φ) (Ctx.dren 0 Γ) := by
    rw [Ctx.dren_zero]; exact wf_unshift hS hw1
  have hX0 : I.Entails (cof Φ φ) ((cof Φ φ).subst (fun n => .var (n + 0))) := by rw [I_add0]; exact ent_refl _
  have e0 := VTy.lineIeq hW hu (k := 0) (r := .neg .zero) (r' := .one) hX0 trivial trivial I_eq_neg_zero hw0
  have e1 := VTy.lineIeq hW hu (k := 0) (r := .neg .one) (r' := .zero) hX0 trivial trivial I_eq_neg_one hw0
  rw [Ctx.dren_zero, sk_one0] at e0
  rw [Ctx.dren_zero, sk_zero0] at e1
  have hT1 : VTy S Ψ (cof Φ φ) Γ (u.dinst .one) (.univ l) := VTy.dsubst' hW .one trivial hu
  have hUφ := VTy.restrict' hW hX (ent_and_left _ _) hU
  have hu0φ := VTy.restrict' hW hX (ent_and_left _ _) hu0
  have eq := VEq.equivCong' hW hUφ hT1 (VEq.lty' hW e1) e0 (VEq.trans' hW e1 hside)
  exact VTy.glue' hW hφ hu0 hT1 (VTy.conv' hW hLE eq)

theorem valid_hcompU_rule (hKT : KTAll S) {u u0 T : Tm} {φ : I} {l : ℕ}
    (h : HasTy0 S Ψ Φ Γ (.hcomp (.univ l) φ u u0) T)
    (hv : Valid2 S Ψ Φ Γ (.hcomp (.univ l) φ u u0) (.hcomp (.univ l) φ u u0) T)
    (hinv : HcompInv S Ψ Φ Γ (.univ l) φ u u0 T) :
    Valid2 S Ψ Φ Γ (.hcomp (.univ l) φ u u0) (Tm.hcompU φ u u0) T := by
  obtain ⟨l0, hφ, hUV, huV, hu0V, hsV, htr, hU, hu, hu0, hside⟩ := hinv
  have hs := scoped_of_ty hU
  have hX : (cof Φ φ).Scoped Ψ := ⟨hs, hφ⟩
  have hX0Φ : I.Entails (cof Φ φ) Φ := ent_and_left _ _
  have hy := VTy.hcompU' hW (KTAt.of_all hKT l) ⟨hU, hUV⟩ hφ ⟨hu, huV⟩ ⟨hu0, hu0V⟩ ⟨hside, hsV⟩
  have hT : ∀ k (c : CSub2 S Ψ Φ Γ k), RT2 S k (c.L T) (c.R T) := fun k c => (hv k c).1
  have hyT := valid_conv_tr hy.v htr hT
  -- where the face holds: the Glue type is the tube's end
  have hyX := VTy.restrict' hW hX hX0Φ hy
  rw [hcompU_eq] at hyX
  have e := VEq.symm' hW (VEq.glueFace' hW (ent_and_right _ _) hyX)
  rw [← hcompU_eq] at e
  have hb := valid_conv_tr e.v (htr.restrict hX0Φ) fun k c => hT k (c.restrictTo hX0Φ)
  refine valid_comp_rule hW hv hyT hb fun k c => ⟨fun hn => ?_, fun hf => ?_⟩
  · have e4 : c.L (Tm.hcompU φ u u0) = Tm.hcompU (φ.subst c.σ.τ) (u.subst (dupS c.γ) (I.up c.σ.τ)) (c.L u0) :=
      hcompU_subst _ _ φ u u0
    have hn' : I.entails .one (φ.subst c.σ.τ) = false := by simpa [I.Entails] using hn
    rw [e4]
    exact ⟨.step (by simp [CSub2.L, Tm.subst, step, hn']) (.refl _), EqTm.hcompU (c.ty hW h)⟩
  · rw [CSub2.L_dinst hW]
    exact ⟨.step (step_hcomp_face hf) (.refl _), EqTm.hcompFace hf (c.ty hW h)⟩

end

end Model.Whnf
