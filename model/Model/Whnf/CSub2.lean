import Model.Whnf.Glue2

/-!
# Related closing substitutions

A related substitution from a context `Ψ; Φ; Γ` into stage `k` is a pair of interval substitutions
that agree up to `I.Eq`, with the face holding, and a pair of term substitutions whose values are
related at the (left) instances of the context's types, which are related themselves.
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

variable {S : Sig} {k k' : ℕ}

/-- Related closing substitutions. -/
structure CSub2 (S : Sig) (Ψ : ℕ) (Φ : I) (Γ : Ctx) (k : ℕ) where
  σ : ISub k Ψ
  σ' : ISub k Ψ
  hσ : ∀ i, I.Eq (σ.τ i) (σ'.τ i)
  γ : ℕ → Tm
  γ' : ℕ → Tm
  face : I.Entails .one (Φ.subst σ.τ)
  look : ∀ x A, Γ.lookup x = some A → RE2 S k (A.subst γ σ.τ) (γ x) (γ' x)
  lookT : ∀ x A, Γ.lookup x = some A → RT2 S k (A.subst γ σ.τ) (A.subst γ' σ'.τ)

namespace CSub2

variable {Ψ : ℕ} {Φ : I} {Γ : Ctx} (c : CSub2 S Ψ Φ Γ k)

/-- The left instance of a term. -/
abbrev L (t : Tm) : Tm := t.subst c.γ c.σ.τ
/-- The right instance of a term. -/
abbrev R (t : Tm) : Tm := t.subst c.γ' c.σ'.τ

theorem face' : I.Entails .one (Φ.subst c.σ'.τ) :=
  ent_trans c.face (eq_ent (I_eq_subst_congr c.hσ Φ))

variable (hW : WfSig S)
include hW

theorem tySubL : TySub S Ψ Φ Γ k .one [] c.γ c.σ.τ :=
  ⟨c.σ.sc, trivial, c.face, fun x A h => spec_to_minimal hW (RE2.typed (c.look x A h)).1, Wf0.nil trivial⟩

theorem tySubR : TySub S Ψ Φ Γ k .one [] c.γ' c.σ'.τ :=
  ⟨c.σ'.sc, trivial, c.face', fun x A h => spec_to_minimal hW
    ((RE2.typed (c.look x A h)).2.1.tyConv (Comp2_ty_base (c.lookT x A h)).2.2.2.2.2), Wf0.nil trivial⟩

theorem eqSub : EqSub S Ψ Γ k .one [] c.γ c.σ.τ c.γ' c.σ'.τ :=
  ⟨fun x A h => spec_to_minimal_eq hW (RE2.typed (c.look x A h)).2.2, fun i _ => c.hσ i⟩

theorem ty {t A : Tm} (h : HasTy0 S Ψ Φ Γ t A) : HasTy S k .one [] (c.L t) (c.L A) :=
  minimal_to_spec ((sub_ty (sigClosed_of_wfSig hW) h).2.1 (c.tySubL hW))

theorem tyR {t A : Tm} (h : HasTy0 S Ψ Φ Γ t A) : HasTy S k .one [] (c.R t) (c.R A) :=
  minimal_to_spec ((sub_ty (sigClosed_of_wfSig hW) h).2.1 (c.tySubR hW))

/-- A typed term at the two instances. -/
theorem eqLR {t A : Tm} (h : HasTy0 S Ψ Φ Γ t A) : EqTm S k .one [] (c.L t) (c.R t) (c.L A) :=
  minimal_to_spec_eq ((sub_ty (sigClosed_of_wfSig hW) h).2.2 (c.tySubL hW) (c.tySubR hW) (c.eqSub hW))

/-- Judgmentally equal terms at the two instances. -/
theorem eq {t u A : Tm} (h : EqTm0 S Ψ Φ Γ t u A) : EqTm S k .one [] (c.L t) (c.R u) (c.L A) := by
  have e1 := minimal_to_spec_eq ((sub_eq (sigClosed_of_wfSig hW) h).2 (c.tySubL hW))
  exact e1.trans (c.eqLR hW (presup hW h).2)

/-- The right instance of a typed term has the left instance of the type. -/
theorem tyR' {t A : Tm} (h : HasTy0 S Ψ Φ Γ t A) : HasTy S k .one [] (c.R t) (c.L A) :=
  HasTy.eqR (c.eqLR hW h)

end CSub2

theorem subst_isub2 (t : Tm) (γ : ℕ → Tm) (τ : ℕ → I) (ρ : ISub k' k) :
    (t.subst γ τ).isub ρ = t.subst (fun x => (γ x).isub ρ) (fun i => (τ i).subst ρ.τ) := by
  simp only [Tm.isub, subst_subst]

/-- The weakening of a closed term by a new interval variable is its restriction along the weakening. -/
theorem dshift_eq_isub_closed {t : Tm} {n : ℕ} (h : t.closedB n k = true) :
    t.isub (ISub.wk k) = t.dshift := by
  rw [dshift_eq, Tm.isub]
  exact closed_subst_eq t n k _ _ _ _ h (fun _ _ => rfl) fun i hi => by simp [ISub.wk, hi]

variable (hW : WfSig S)
include hW

theorem RE2.dshift {A t t' : Tm} (h : RE2 S k A t t') : RE2 S (k + 1) A.dshift t.dshift t'.dshift := by
  have hE := RE2.typed h
  have := RE2.isub hW h (ISub.wk k)
  rwa [dshift_eq_isub_closed (closed_of_isTyK hW (isTyK_of_ty hW hE.1)), dshift_eq_isub_closed (closed_of_ty hW hE.1),
    dshift_eq_isub_closed (closed_of_ty hW hE.2.1)] at this

theorem RT2.dshift {A A' : Tm} (hX : TyCode k (semK S k A)) (h : RT2 S k A A') : RT2 S (k + 1) A.dshift A'.dshift := by
  have hb := Comp2_ty_base h
  have := RT2.isub hW hX h (ISub.wk k)
  rwa [dshift_eq_isub_closed (closed_of_isTyK hW hb.2.1), dshift_eq_isub_closed (closed_of_isTyK hW hb.2.2.1)] at this

namespace CSub2

variable {Ψ : ℕ} {Φ : I} {Γ : Ctx}

theorem tyCode_look (c : CSub2 S Ψ Φ Γ k) {x : ℕ} {A : Tm} (h : Γ.lookup x = some A) :
    TyCode k (semK S k (A.subst c.γ c.σ.τ)) :=
  RE2.tyCode hW (c.look x A h)

/-- Restriction of a related substitution. -/
def restr (c : CSub2 S Ψ Φ Γ k) (ρ : ISub k' k) : CSub2 S Ψ Φ Γ k' where
  σ := c.σ.comp ρ
  σ' := c.σ'.comp ρ
  hσ i := I_eq_subst (c.hσ i) ρ.τ
  γ x := (c.γ x).isub ρ
  γ' x := (c.γ' x).isub ρ
  face := by
    have := ent_subst c.face ρ.τ
    rwa [I_subst_subst] at this
  look x A h := by
    have := RE2.isub hW (c.look x A h) ρ
    rwa [subst_isub2] at this
  lookT x A h := by
    have := RT2.isub hW (c.tyCode_look hW h) (c.lookT x A h) ρ
    rwa [subst_isub2, subst_isub2] at this

theorem restr_L (c : CSub2 S Ψ Φ Γ k) (ρ : ISub k' k) (t : Tm) : (c.restr hW ρ).L t = (c.L t).isub ρ :=
  (subst_isub2 _ _ _ _).symm

theorem restr_R (c : CSub2 S Ψ Φ Γ k) (ρ : ISub k' k) (t : Tm) : (c.restr hW ρ).R t = (c.R t).isub ρ :=
  (subst_isub2 _ _ _ _).symm

/-- Extension of a related substitution by related elements of a related type. -/
def ext (c : CSub2 S Ψ Φ Γ k) (A a a' : Tm) (ha : RE2 S k (c.L A) a a') (hA : RT2 S k (c.L A) (c.R A)) :
    CSub2 S Ψ Φ (A :: Γ) k where
  σ := c.σ
  σ' := c.σ'
  hσ := c.hσ
  γ := consT a c.γ
  γ' := consT a' c.γ'
  face := c.face
  look x B h := by
    cases x with
    | zero =>
      simp only [Ctx.lookup, Option.some.injEq] at h; subst h
      rw [shift_consT]; exact ha
    | succ x =>
      simp only [Ctx.lookup, Option.map_eq_some_iff] at h
      obtain ⟨B', hB', rfl⟩ := h
      rw [shift_consT]; exact c.look x B' hB'
  lookT x B h := by
    cases x with
    | zero =>
      simp only [Ctx.lookup, Option.some.injEq] at h; subst h
      rw [shift_consT, shift_consT]; exact hA
    | succ x =>
      simp only [Ctx.lookup, Option.map_eq_some_iff] at h
      obtain ⟨B', hB', rfl⟩ := h
      rw [shift_consT, shift_consT]; exact c.lookT x B' hB'

/-- Instantiation of a line context at equal interval terms. -/
def cons (c : CSub2 S Ψ Φ Γ k) (r r' : I) (hr : r.Scoped k) (hr' : r'.Scoped k) (he : I.Eq r r') :
    CSub2 S (Ψ + 1) Φ.shift Γ.dshift k where
  σ := ISub.cons r hr c.σ
  σ' := ISub.cons r' hr' c.σ'
  hσ i := by
    cases i with
    | zero => exact he
    | succ i => exact c.hσ i
  γ := c.γ
  γ' := c.γ'
  face := by
    show I.Entails .one (Φ.shift.subst (consI r c.σ.τ))
    rw [I.shift, I_ren_subst]; exact c.face
  look x B h := by
    rw [lookup_dshift, Option.map_eq_some_iff] at h
    obtain ⟨B', hB', rfl⟩ := h
    show RE2 S k (B'.dshift.subst c.γ (consI r c.σ.τ)) (c.γ x) (c.γ' x)
    rw [dshift_consI]; exact c.look x B' hB'
  lookT x B h := by
    rw [lookup_dshift, Option.map_eq_some_iff] at h
    obtain ⟨B', hB', rfl⟩ := h
    show RT2 S k (B'.dshift.subst c.γ (consI r c.σ.τ)) (B'.dshift.subst c.γ' (consI r' c.σ'.τ))
    rw [dshift_consI, dshift_consI]; exact c.lookT x B' hB'

/-- Lifting a related substitution under an interval binder. -/
def up (c : CSub2 S Ψ Φ Γ k) : CSub2 S (Ψ + 1) Φ.shift Γ.dshift (k + 1) where
  σ := c.σ.up
  σ' := c.σ'.up
  hσ i := by
    cases i with
    | zero => exact I_eq_refl _
    | succ i =>
      show I.Eq (c.σ.τ i).shift (c.σ'.τ i).shift
      exact fun ρ => by rw [I.shift, I.shift, eval_ren, eval_ren]; exact c.hσ i _
  γ x := (c.γ x).dshift
  γ' x := (c.γ' x).dshift
  face := by
    show I.Entails .one (Φ.shift.subst (I.up c.σ.τ))
    rw [I_shift_subst_up]; exact ent_shift c.face
  look x B h := by
    rw [lookup_dshift, Option.map_eq_some_iff] at h
    obtain ⟨B', hB', rfl⟩ := h
    show RE2 S (k + 1) (B'.dshift.subst (dupS c.γ) (I.up c.σ.τ)) (c.γ x).dshift (c.γ' x).dshift
    rw [dshift_dup_subst]; exact RE2.dshift hW (c.look x B' hB')
  lookT x B h := by
    rw [lookup_dshift, Option.map_eq_some_iff] at h
    obtain ⟨B', hB', rfl⟩ := h
    show RT2 S (k + 1) (B'.dshift.subst (dupS c.γ) (I.up c.σ.τ)) (B'.dshift.subst (dupS c.γ') (I.up c.σ'.τ))
    rw [dshift_dup_subst, dshift_dup_subst]; exact RT2.dshift hW (c.tyCode_look hW hB') (c.lookT x B' hB')

/-- Extending the face by a face that holds. -/
def cof (c : CSub2 S Ψ Φ Γ k) {φ : I} (h : I.Entails .one (φ.subst c.σ.τ)) :
    CSub2 S Ψ (KubusCore.cof Φ φ) Γ k :=
  { c with face := ent_and_intro c.face h }

/-- Restricting to a smaller face. -/
def restrictTo {Φ' : I} (he : I.Entails Φ' Φ) (c : CSub2 S Ψ Φ' Γ k) : CSub2 S Ψ Φ Γ k :=
  { c with face := ent_trans c.face (ent_subst he _) }

/-- The left instance on both sides. -/
def diagL (c : CSub2 S Ψ Φ Γ k) : CSub2 S Ψ Φ Γ k where
  σ := c.σ
  σ' := c.σ
  hσ i := I_eq_refl _
  γ := c.γ
  γ' := c.γ
  face := c.face
  look x A h := (perK hW (c.tyCode_look hW h)).reflEl (c.lookT x A h) (c.look x A h)
  lookT x A h := RT2.refl hW (c.tyCode_look hW h) (c.lookT x A h)

/-- The right instance on both sides. -/
def diagR (c : CSub2 S Ψ Φ Γ k) : CSub2 S Ψ Φ Γ k where
  σ := c.σ'
  σ' := c.σ'
  hσ i := I_eq_refl _
  γ := c.γ'
  γ' := c.γ'
  face := c.face'
  look x A h := RE2.conv hW (c.lookT x A h)
    ((perK hW (c.tyCode_look hW h)).reflEl' (c.lookT x A h) (c.look x A h))
  lookT x A h := RT2.refl' hW (c.tyCode_look hW h) (c.lookT x A h)

theorem up_restr_L (c : CSub2 S Ψ Φ Γ k) (ρ : ISub k' k) (t : Tm) :
    ((c.restr hW ρ).up hW).L t = ((c.up hW).L t).isub ρ.up := by
  simp only [L, up, restr, Tm.isub, subst_subst, ISub.up, ISub.comp]
  apply subst_congr
  · intro x; exact (isub_dshift (c.γ x) ρ).symm
  · intro i; exact (I_up_comp _ _ i).symm

theorem up_restr_R (c : CSub2 S Ψ Φ Γ k) (ρ : ISub k' k) (t : Tm) :
    ((c.restr hW ρ).up hW).R t = ((c.up hW).R t).isub ρ.up := by
  simp only [R, up, restr, Tm.isub, subst_subst, ISub.up, ISub.comp]
  apply subst_congr
  · intro x; exact (isub_dshift (c.γ' x) ρ).symm
  · intro i; exact (I_up_comp _ _ i).symm

theorem cons_restr_L (c : CSub2 S Ψ Φ Γ k) (ρ : ISub k' k) (r r' : I) (hr : r.Scoped k') (hr' : r'.Scoped k')
    (he : I.Eq r r') (t : Tm) :
    ((c.restr hW ρ).cons r r' hr hr' he).L t = (((c.up hW).L t).isub ρ.up).dinst r := by
  rw [← up_restr_L]
  exact (dup_dinst t _ _ r).symm

theorem cons_restr_R (c : CSub2 S Ψ Φ Γ k) (ρ : ISub k' k) (r r' : I) (hr : r.Scoped k') (hr' : r'.Scoped k')
    (he : I.Eq r r') (t : Tm) :
    ((c.restr hW ρ).cons r r' hr hr' he).R t = (((c.up hW).R t).isub ρ.up).dinst r' := by
  rw [← up_restr_R]
  exact (dup_dinst t _ _ r').symm

end CSub2

end

end Model.Whnf
