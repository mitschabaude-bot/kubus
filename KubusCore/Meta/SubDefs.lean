import KubusCore.Meta.Weaken

/-!
# Metatheory: typed substitutions

`TySub` says that `(σ, τ)` maps `Ψ; Φ; Γ` to `Ψ'; Φ'; Δ`: interval terms are scoped, the target
restriction entails the substituted source restriction, and every variable is sent to a term
of the substituted type. `EqSub` says two substitutions are equal (judgmentally on term
variables, in the free De Morgan algebra on interval variables), `FaceEq` that two interval
substitutions agree on every face of the target restriction.

`SubP`, `FunP`, `FaceP` are the substitution, functionality and face-functionality properties
of a single judgment `X : T`; `CtxSub` collects them for the types of a context.
-/

namespace KubusCore.Meta

open Tm

variable {S : Sig}

structure TySub (S : Sig) (Ψ : Nat) (Φ : I) (Γ : Ctx) (Ψ' : Nat) (Φ' : I) (Δ : Ctx)
    (σ : Nat → Tm) (τ : Nat → I) : Prop where
  bound : ∀ i < Ψ, (τ i).Scoped Ψ'
  hscoped : Φ'.Scoped Ψ'
  ent : I.Entails Φ' (Φ.subst τ)
  look : ∀ x A, Γ.lookup x = some A → HasTy0 S Ψ' Φ' Δ (σ x) (A.subst σ τ)
  wf : Wf0 S Ψ' Φ' Δ

def EqSub (S : Sig) (Ψ : Nat) (Γ : Ctx) (Ψ' : Nat) (Φ' : I) (Δ : Ctx)
    (σ1 : Nat → Tm) (τ1 : Nat → I) (σ2 : Nat → Tm) (τ2 : Nat → I) : Prop :=
  (∀ x A, Γ.lookup x = some A → EqTm0 S Ψ' Φ' Δ (σ1 x) (σ2 x) (A.subst σ1 τ1)) ∧
  (∀ i < Ψ, I.Eq (τ1 i) (τ2 i))

def FaceEq (Ψ : Nat) (Ξ : I) (τ1 τ2 : Nat → I) : Prop :=
  ∀ i < Ψ, ∀ α ∈ Ξ.faces, I.Eq ((τ1 i).subst (faceSub α)) ((τ2 i).subst (faceSub α))

def SubP (S : Sig) (Ψ : Nat) (Φ : I) (Γ : Ctx) (X T : Tm) : Prop :=
  ∀ {Ψ' Φ' Δ σ τ}, TySub S Ψ Φ Γ Ψ' Φ' Δ σ τ → HasTy0 S Ψ' Φ' Δ (X.subst σ τ) (T.subst σ τ)

def FunP (S : Sig) (Ψ : Nat) (Φ : I) (Γ : Ctx) (X T : Tm) : Prop :=
  ∀ {Ψ' Φ' Δ σ1 τ1 σ2 τ2}, TySub S Ψ Φ Γ Ψ' Φ' Δ σ1 τ1 → TySub S Ψ Φ Γ Ψ' Φ' Δ σ2 τ2 →
    EqSub S Ψ Γ Ψ' Φ' Δ σ1 τ1 σ2 τ2 → EqTm0 S Ψ' Φ' Δ (X.subst σ1 τ1) (X.subst σ2 τ2) (T.subst σ1 τ1)

def FaceP (S : Sig) (Ψ : Nat) (Φ : I) (Γ : Ctx) (X T : Tm) : Prop :=
  ∀ {Ψ' Φ' Δ σ τ1 τ2}, TySub S Ψ Φ Γ Ψ' Φ' Δ σ τ1 → TySub S Ψ Φ Γ Ψ' Φ' Δ σ τ2 →
    FaceEq Ψ Φ' τ1 τ2 → EqTm0 S Ψ' Φ' Δ (X.subst σ τ1) (X.subst σ τ2) (T.subst σ τ1)

def CtxSub (S : Sig) (Ψ : Nat) (Φ : I) : Ctx → Prop
  | [] => True
  | A :: Γ => CtxSub S Ψ Φ Γ ∧ ∃ l, SubP S Ψ Φ Γ A (univ l) ∧ FunP S Ψ Φ Γ A (univ l) ∧
      FaceP S Ψ Φ Γ A (univ l)

/-! ## Restrictions -/

theorem Wf0.dwk (hS : SigClosed S) {Ψ Φ Γ} (h : Wf0 S Ψ Φ Γ) : Wf0 S (Ψ + 1) Φ.shift Γ.dshift := by
  have := (wfAll_of_wf hS h).wk 1 (Φ1 := Φ.shift) (ent_refl _)
  rw [Ctx_dshift_eq]
  exact this.wf (scoped_shift (scoped_of_wf h))

theorem TySub.restrictSrc {Ψ Φ Γ Ψ' Φ' Δ σ τ Φ1} (h : TySub S Ψ Φ1 Γ Ψ' Φ' Δ σ τ)
    (he : I.Entails Φ1 Φ) : TySub S Ψ Φ Γ Ψ' Φ' Δ σ τ :=
  ⟨h.bound, h.hscoped, ent_trans h.ent (ent_subst he _), h.look, h.wf⟩

theorem TySub.restrict {Ψ Φ Γ Ψ' Φ' Δ σ τ Ξ} (h : TySub S Ψ Φ Γ Ψ' Φ' Δ σ τ)
    (hs : Ξ.Scoped Ψ') (he : I.Entails Ξ Φ') : TySub S Ψ Φ Γ Ψ' Ξ Δ σ τ :=
  ⟨h.bound, hs, ent_trans he h.ent, fun x A hx => HasTy0.restrict hs he (h.look x A hx),
    h.wf.restrict hs he⟩

theorem TySub.sc {Ψ Φ Γ Ψ' Φ' Δ σ τ} (h : TySub S Ψ Φ Γ Ψ' Φ' Δ σ τ) {r : I} (hr : r.Scoped Ψ) :
    (r.subst τ).Scoped Ψ' := scoped_subst hr h.bound

theorem TySub.underCof {Ψ Φ Γ Ψ' Φ' Δ σ τ} (h : TySub S Ψ Φ Γ Ψ' Φ' Δ σ τ) {φ : I}
    (hφ : φ.Scoped Ψ) : TySub S Ψ (cof Φ φ) Γ Ψ' (cof Φ' (φ.subst τ)) Δ σ τ :=
  { bound := h.bound
    hscoped := ⟨h.hscoped, h.sc hφ⟩
    ent := ent_and_mono h.ent (ent_refl _)
    look := fun x A hx => HasTy0.restrict ⟨h.hscoped, h.sc hφ⟩ (ent_and_left _ _) (h.look x A hx)
    wf := h.wf.restrict ⟨h.hscoped, h.sc hφ⟩ (ent_and_left _ _) }

theorem EqSub.restrict {Ψ Γ Ψ' Φ' Δ σ1 τ1 σ2 τ2 Ξ} (h : EqSub S Ψ Γ Ψ' Φ' Δ σ1 τ1 σ2 τ2)
    (hs : Ξ.Scoped Ψ') (he : I.Entails Ξ Φ') : EqSub S Ψ Γ Ψ' Ξ Δ σ1 τ1 σ2 τ2 :=
  ⟨fun x A hx => EqTm0.restrict hs he (h.1 x A hx), h.2⟩

theorem SubP.restrictSrc {Ψ Φ Γ X T Φ1} (h : SubP S Ψ Φ Γ X T) (he : I.Entails Φ1 Φ) :
    SubP S Ψ Φ1 Γ X T := fun hσ => h (hσ.restrictSrc he)

theorem FunP.restrictSrc {Ψ Φ Γ X T Φ1} (h : FunP S Ψ Φ Γ X T) (he : I.Entails Φ1 Φ) :
    FunP S Ψ Φ1 Γ X T := fun h1 h2 he' => h (h1.restrictSrc he) (h2.restrictSrc he) he'

theorem FaceP.restrictSrc {Ψ Φ Γ X T Φ1} (h : FaceP S Ψ Φ Γ X T) (he : I.Entails Φ1 Φ) :
    FaceP S Ψ Φ1 Γ X T := fun h1 h2 he' => h (h1.restrictSrc he) (h2.restrictSrc he) he'

theorem CtxSub.restrictSrc {Ψ Φ Φ1} (he : I.Entails Φ1 Φ) : ∀ {Γ}, CtxSub S Ψ Φ Γ → CtxSub S Ψ Φ1 Γ
  | [], _ => trivial
  | _ :: _, ⟨h1, l, h2, h3, h4⟩ =>
    ⟨CtxSub.restrictSrc he h1, l, h2.restrictSrc he, h3.restrictSrc he, h4.restrictSrc he⟩

/-! ## Lifting under binders -/

theorem TySub.tail {Ψ Φ A Γ Ψ' Φ' Δ σ τ} (h : TySub S Ψ Φ (A :: Γ) Ψ' Φ' Δ σ τ) :
    TySub S Ψ Φ Γ Ψ' Φ' Δ (fun n => σ (n + 1)) τ :=
  { bound := h.bound, hscoped := h.hscoped, ent := h.ent, wf := h.wf
    look := fun x B hx => by
      have := h.look (x + 1) B.shift (by simp [Ctx.lookup, hx])
      rwa [shift_subst] at this }

theorem shift_up_subst (A : Tm) (σ : Nat → Tm) (τ : Nat → I) :
    A.shift.subst (up σ) τ = (A.subst σ τ).shift := by
  rw [shift_subst, subst_shift]; rfl

/-- Lift under a term binder, with a target type judgmentally equal to the substituted one. -/
theorem TySub.up (hS : SigClosed S) {Ψ Φ Γ Ψ' Φ' Δ σ τ} (h : TySub S Ψ Φ Γ Ψ' Φ' Δ σ τ) {A A' : Tm}
    {l : Nat} (hA' : HasTy0 S Ψ' Φ' Δ A' (univ l)) (he : EqTm0 S Ψ' Φ' Δ A' (A.subst σ τ) (univ l)) :
    TySub S Ψ Φ (A :: Γ) Ψ' Φ' (A' :: Δ) (Tm.up σ) τ :=
  { bound := h.bound, hscoped := h.hscoped, ent := h.ent
    wf := Wf0.cons hA'
    look := fun x B hx => by
      cases x with
      | zero =>
        simp only [Ctx.lookup, Option.some.injEq] at hx; subst hx
        rw [shift_up_subst]
        exact HasTy0.conv (HasTy0.var (Wf0.cons hA') rfl) (EqTm0.wk hS hA' he)
      | succ x =>
        simp only [Ctx.lookup, Option.map_eq_some_iff] at hx
        obtain ⟨B0, hB0, rfl⟩ := hx
        rw [shift_up_subst]
        exact HasTy0.wk hS hA' (h.look x B0 hB0) }

theorem TySub.up' (hS : SigClosed S) {Ψ Φ Γ Ψ' Φ' Δ σ τ} (h : TySub S Ψ Φ Γ Ψ' Φ' Δ σ τ) {A : Tm}
    {l : Nat} (hA : HasTy0 S Ψ' Φ' Δ (A.subst σ τ) (univ l)) :
    TySub S Ψ Φ (A :: Γ) Ψ' Φ' (A.subst σ τ :: Δ) (Tm.up σ) τ :=
  h.up hS hA (EqTm0.refl hA)

theorem EqSub.up (hS : SigClosed S) {Ψ Φ Γ Ψ' Φ' Δ σ1 τ1 σ2 τ2} (h1 : TySub S Ψ Φ Γ Ψ' Φ' Δ σ1 τ1)
    (h : EqSub S Ψ Γ Ψ' Φ' Δ σ1 τ1 σ2 τ2) {A A' : Tm} {l : Nat} (hA' : HasTy0 S Ψ' Φ' Δ A' (univ l))
    (he : EqTm0 S Ψ' Φ' Δ A' (A.subst σ1 τ1) (univ l)) :
    EqSub S Ψ (A :: Γ) Ψ' Φ' (A' :: Δ) (Tm.up σ1) τ1 (Tm.up σ2) τ2 :=
  ⟨fun x B hx => by
    cases x with
    | zero =>
      simp only [Ctx.lookup, Option.some.injEq] at hx; subst hx
      exact EqTm0.refl ((h1.up hS hA' he).look 0 _ rfl)
    | succ x =>
      simp only [Ctx.lookup, Option.map_eq_some_iff] at hx
      obtain ⟨B0, hB0, rfl⟩ := hx
      rw [shift_up_subst]
      exact EqTm0.wk hS hA' (h.1 x B0 hB0), h.2⟩

theorem Iup_scoped {τ : Nat → I} {Ψ Ψ' : Nat} (h : ∀ i < Ψ, (τ i).Scoped Ψ') :
    ∀ i < Ψ + 1, (I.up τ i).Scoped (Ψ' + 1) := by
  intro i hi; cases i with
  | zero => show 0 < Ψ' + 1; omega
  | succ i => exact scoped_shift (h i (by omega))

theorem dshift_dup_subst (A : Tm) (σ : Nat → Tm) (τ : Nat → I) :
    A.dshift.subst (dupS σ) (I.up τ) = (A.subst σ τ).dshift := by
  rw [dshift_subst, subst_dshift]; rfl

theorem Ishift_up_subst (r : I) (τ : Nat → I) : r.shift.subst (I.up τ) = (r.subst τ).shift :=
  I_shift_subst_up τ r

theorem lookup_dshift (Γ : Ctx) (x : Nat) : Γ.dshift.lookup x = (Γ.lookup x).map Tm.dshift :=
  lookup_map (fun t => shift_dshift t |>.symm) x

/-- Lift under an interval binder. -/
theorem TySub.dup (hS : SigClosed S) {Ψ Φ Γ Ψ' Φ' Δ σ τ} (h : TySub S Ψ Φ Γ Ψ' Φ' Δ σ τ) :
    TySub S (Ψ + 1) Φ.shift Γ.dshift (Ψ' + 1) Φ'.shift Δ.dshift (dupS σ) (I.up τ) :=
  { bound := Iup_scoped h.bound
    hscoped := scoped_shift h.hscoped
    ent := by rw [Ishift_up_subst]; exact ent_shift h.ent
    wf := h.wf.dwk hS
    look := fun x A hx => by
      rw [lookup_dshift, Option.map_eq_some_iff] at hx
      obtain ⟨A0, hA0, rfl⟩ := hx
      rw [dshift_dup_subst]
      exact HasTy0.dwk hS (h.look x A0 hA0) }

theorem EqSub.dup (hS : SigClosed S) {Ψ Γ Ψ' Φ' Δ σ1 τ1 σ2 τ2} (h : EqSub S Ψ Γ Ψ' Φ' Δ σ1 τ1 σ2 τ2) :
    EqSub S (Ψ + 1) Γ.dshift (Ψ' + 1) Φ'.shift Δ.dshift (dupS σ1) (I.up τ1) (dupS σ2) (I.up τ2) :=
  ⟨fun x A hx => by
    rw [lookup_dshift, Option.map_eq_some_iff] at hx
    obtain ⟨A0, hA0, rfl⟩ := hx
    rw [dshift_dup_subst]
    exact EqTm0.dwk hS (h.1 x A0 hA0),
   fun i hi => by
    cases i with
    | zero => exact I_eq_refl _
    | succ i => exact I_eq_subst (h.2 i (by omega)) _⟩

/-- Instantiate the interval binder of a line context by `r`. -/
def consI (r : I) (τ : Nat → I) : Nat → I
  | 0 => r
  | n + 1 => τ n

theorem dshift_consI (A : Tm) (σ : Nat → Tm) (r : I) (τ : Nat → I) :
    A.dshift.subst σ (consI r τ) = A.subst σ τ := by
  rw [dshift_subst]; rfl

theorem TySub.inst {Ψ Φ Γ Ψ' Φ' Δ σ τ} (h : TySub S Ψ Φ Γ Ψ' Φ' Δ σ τ) {r : I} (hr : r.Scoped Ψ') :
    TySub S (Ψ + 1) Φ.shift Γ.dshift Ψ' Φ' Δ σ (consI r τ) :=
  { bound := fun i hi => by cases i with
      | zero => exact hr
      | succ i => exact h.bound i (by omega)
    hscoped := h.hscoped
    ent := by
      have : Φ.shift.subst (consI r τ) = Φ.subst τ := by simp only [I.shift, I.ren, I_subst_subst]; rfl
      rw [this]; exact h.ent
    wf := h.wf
    look := fun x A hx => by
      rw [lookup_dshift, Option.map_eq_some_iff] at hx
      obtain ⟨A0, hA0, rfl⟩ := hx
      rw [dshift_consI]
      exact h.look x A0 hA0 }

theorem EqSub.inst {Ψ Γ Ψ' Φ' Δ σ1 τ1 σ2 τ2} (h : EqSub S Ψ Γ Ψ' Φ' Δ σ1 τ1 σ2 τ2) {r r' : I}
    (hr : I.Eq r r') : EqSub S (Ψ + 1) Γ.dshift Ψ' Φ' Δ σ1 (consI r τ1) σ2 (consI r' τ2) :=
  ⟨fun x A hx => by
    rw [lookup_dshift, Option.map_eq_some_iff] at hx
    obtain ⟨A0, hA0, rfl⟩ := hx
    rw [dshift_consI]
    exact h.1 x A0 hA0,
   fun i hi => by
    cases i with
    | zero => exact hr
    | succ i => exact h.2 i (by omega)⟩

theorem dinst_consI (A : Tm) (r : I) (σ : Nat → Tm) (τ : Nat → I) :
    (A.dinst r).subst σ τ = A.subst σ (consI (r.subst τ) τ) := by
  simp only [Tm.dinst, Tm.dsubst, subst_subst]
  apply subst_congr
  · intro n; rfl
  · intro i; cases i <;> rfl

end KubusCore.Meta
