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

/-- Interval substitutions agreeing up to `I.Eq`. -/
def INear {Ψ : ℕ} (τ τ' : ISub k Ψ) : Prop := ∀ i, I.Eq (τ.τ i) (τ'.τ i)

theorem INear.refl {Ψ : ℕ} (τ : ISub k Ψ) : INear τ τ := fun _ => I_eq_refl _
theorem INear.symm {Ψ : ℕ} {τ τ' : ISub k Ψ} (h : INear τ τ') : INear τ' τ := fun i => I_eq_symm (h i)
theorem INear.trans {Ψ : ℕ} {τ τ' τ'' : ISub k Ψ} (h : INear τ τ') (h' : INear τ' τ'') : INear τ τ'' :=
  fun i => I_eq_trans (h i) (h' i)
theorem INear.comp {Ψ : ℕ} {τ τ' : ISub k Ψ} (h : INear τ τ') (ρ : ISub k' k) : INear (τ.comp ρ) (τ'.comp ρ) :=
  fun i => I_eq_subst (h i) ρ.τ

/-- A type whose instances are related at all restrictions, all nearby interval substitutions, and
either of two term substitutions on each side. -/
def TyRob (S : Sig) {Ψ : ℕ} (A : Tm) (σ : ISub k Ψ) (γ γ' : ℕ → Tm) : Prop :=
  ∀ k' (ρ : ISub k' k) (τ1 τ2 : ISub k' Ψ), INear (σ.comp ρ) τ1 → INear (σ.comp ρ) τ2 → ∀ b1 b2 : Bool,
    RT2 S k' (A.subst (fun y => (cond b1 γ γ' y).isub ρ) τ1.τ) (A.subst (fun y => (cond b2 γ γ' y).isub ρ) τ2.τ)

/-- Related closing substitutions. -/
structure CSub2 (S : Sig) (Ψ : ℕ) (Φ : I) (Γ : Ctx) (k : ℕ) where
  σ : ISub k Ψ
  σ' : ISub k Ψ
  hσ : INear σ σ'
  γ : ℕ → Tm
  γ' : ℕ → Tm
  hγ : ∀ y, (γ y).isub (ISub.id k) = γ y
  hγ' : ∀ y, (γ' y).isub (ISub.id k) = γ' y
  face : I.Entails .one (Φ.subst σ.τ)
  look : ∀ x A, Γ.lookup x = some A → RE2 S k (A.subst γ σ.τ) (γ x) (γ' x)
  lookT : ∀ x A, Γ.lookup x = some A → TyRob S A σ γ γ'

namespace CSub2

variable {Ψ : ℕ} {Φ : I} {Γ : Ctx} (c : CSub2 S Ψ Φ Γ k)

/-- The left instance of a term. -/
abbrev L (t : Tm) : Tm := t.subst c.γ c.σ.τ
/-- The right instance of a term. -/
abbrev R (t : Tm) : Tm := t.subst c.γ' c.σ'.τ

theorem face' : I.Entails .one (Φ.subst c.σ'.τ) :=
  ent_trans c.face (eq_ent (I_eq_subst_congr c.hσ Φ))

omit c in
theorem cond_isub_id (c : CSub2 S Ψ Φ Γ k) (b : Bool) : (fun y => (cond b c.γ c.γ' y).isub (ISub.id k)) = cond b c.γ c.γ' := by
  funext y; cases b
  · exact c.hγ' y
  · exact c.hγ y

/-- The instances of a context type at nearby interval substitutions are related. -/
theorem lookT0 {x : ℕ} {A : Tm} (h : Γ.lookup x = some A) {τ1 τ2 : ISub k Ψ} (h1 : INear c.σ τ1) (h2 : INear c.σ τ2)
    (b1 b2 : Bool) : RT2 S k (A.subst (cond b1 c.γ c.γ') τ1.τ) (A.subst (cond b2 c.γ c.γ') τ2.τ) := by
  have := c.lookT x A h k (ISub.id k) τ1 τ2 (by rw [ISub.comp_id]; exact h1) (by rw [ISub.comp_id]; exact h2) b1 b2
  rwa [c.cond_isub_id, c.cond_isub_id] at this

/-- The left and right instances of a context type are related. -/
theorem lookT' {x : ℕ} {A : Tm} (h : Γ.lookup x = some A) : RT2 S k (A.subst c.γ c.σ.τ) (A.subst c.γ' c.σ'.τ) :=
  c.lookT0 h (INear.refl _) c.hσ true false

variable (hW : WfSig S)
include hW

theorem tySubL : TySub S Ψ Φ Γ k .one [] c.γ c.σ.τ :=
  ⟨c.σ.sc, trivial, c.face, fun x A h => spec_to_minimal hW (RE2.typed (c.look x A h)).1, Wf0.nil trivial⟩

theorem tySubR : TySub S Ψ Φ Γ k .one [] c.γ' c.σ'.τ :=
  ⟨c.σ'.sc, trivial, c.face', fun x A h => spec_to_minimal hW
    ((RE2.typed (c.look x A h)).2.1.tyConv (Comp2_ty_base (c.lookT' h)).2.2.2.2.2), Wf0.nil trivial⟩

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
  hσ := c.hσ.comp ρ
  γ x := (c.γ x).isub ρ
  γ' x := (c.γ' x).isub ρ
  hγ y := by rw [Tm.isub_isub, ISub.comp_id]
  hγ' y := by rw [Tm.isub_isub, ISub.comp_id]
  face := by
    have := ent_subst c.face ρ.τ
    rwa [I_subst_subst] at this
  look x A h := by
    have := RE2.isub hW (c.look x A h) ρ
    rwa [subst_isub2] at this
  lookT x A h k'' ρ' τ1 τ2 h1 h2 b1 b2 := by
    have e : ∀ b : Bool, (fun y => (cond b (fun x => (c.γ x).isub ρ) (fun x => (c.γ' x).isub ρ) y).isub ρ') =
        fun y => (cond b c.γ c.γ' y).isub (ρ.comp ρ') := by
      intro b; funext y; cases b <;> exact Tm.isub_isub _ _ _
    rw [e, e]
    rw [ISub.comp_assoc] at h1 h2
    exact c.lookT x A h k'' (ρ.comp ρ') τ1 τ2 h1 h2 b1 b2

theorem restr_L (c : CSub2 S Ψ Φ Γ k) (ρ : ISub k' k) (t : Tm) : (c.restr hW ρ).L t = (c.L t).isub ρ :=
  (subst_isub2 _ _ _ _).symm

theorem restr_R (c : CSub2 S Ψ Φ Γ k) (ρ : ISub k' k) (t : Tm) : (c.restr hW ρ).R t = (c.R t).isub ρ :=
  (subst_isub2 _ _ _ _).symm

omit hW in
theorem cond_consT (b : Bool) (a a' : Tm) (γ γ' : ℕ → Tm) (y : ℕ) :
    cond b (consT a γ) (consT a' γ') (y + 1) = cond b γ γ' y := by
  cases b <;> rfl

/-- Extension of a related substitution by related elements of a related type. -/
def ext (c : CSub2 S Ψ Φ Γ k) (A a a' : Tm) (ha : RE2 S k (c.L A) a a') (hA : TyRob S A c.σ c.γ c.γ') :
    CSub2 S Ψ Φ (A :: Γ) k where
  σ := c.σ
  σ' := c.σ'
  hσ := c.hσ
  γ := consT a c.γ
  γ' := consT a' c.γ'
  hγ y := by
    cases y with
    | zero => exact isub_id_of_closed (closed_of_ty hW (RE2.typed ha).1)
    | succ y => exact c.hγ y
  hγ' y := by
    cases y with
    | zero => exact isub_id_of_closed (closed_of_ty hW (RE2.typed ha).2.1)
    | succ y => exact c.hγ' y
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
  lookT x B h k' ρ τ1 τ2 h1 h2 b1 b2 := by
    have e : ∀ (C : Tm) (b : Bool) (τ : ISub k' Ψ),
        C.shift.subst (fun y => (cond b (consT a c.γ) (consT a' c.γ') y).isub ρ) τ.τ =
          C.subst (fun y => (cond b c.γ c.γ' y).isub ρ) τ.τ := by
      intro C b τ; rw [shift_subst]; simp only [cond_consT]
    cases x with
    | zero =>
      simp only [Ctx.lookup, Option.some.injEq] at h; subst h
      rw [e, e]; exact hA k' ρ τ1 τ2 h1 h2 b1 b2
    | succ x =>
      simp only [Ctx.lookup, Option.map_eq_some_iff] at h
      obtain ⟨B', hB', rfl⟩ := h
      rw [e, e]; exact c.lookT x B' hB' k' ρ τ1 τ2 h1 h2 b1 b2

omit hW in
theorem id_up : (ISub.id k).up = ISub.id (k + 1) := by
  ext i
  cases i with
  | zero => simp [ISub.up, ISub.id, I.up]
  | succ i =>
    show (if i < k then I.var i else I.zero).shift = if i + 1 < k + 1 then I.var (i + 1) else I.zero
    by_cases h : i < k
    · simp [h, I.shift, I.ren, I.subst]
    · simp [h, I.shift, I.ren, I.subst]

omit hW in
theorem dshift_isub (t : Tm) (ρ : ISub k' (k + 1)) : t.dshift.isub ρ = t.isub ρ.tail := by
  simp only [Tm.isub, dshift_subst]; rfl

omit hW in
theorem cons_comp_tail (σ : ISub k Ψ) (r : I) (hr : r.Scoped k) (ρ : ISub k' k) :
    ((ISub.cons r hr σ).comp ρ).tail = σ.comp ρ := by
  ext i; rfl

omit hW in
theorem INear.tail {τ τ' : ISub k (Ψ + 1)} (h : INear τ τ') : INear τ.tail τ'.tail := fun i => h (i + 1)

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
  hγ := c.hγ
  hγ' := c.hγ'
  face := by
    show I.Entails .one (Φ.shift.subst (consI r c.σ.τ))
    rw [I.shift, I_ren_subst]; exact c.face
  look x B h := by
    rw [lookup_dshift, Option.map_eq_some_iff] at h
    obtain ⟨B', hB', rfl⟩ := h
    show RE2 S k (B'.dshift.subst c.γ (consI r c.σ.τ)) (c.γ x) (c.γ' x)
    rw [dshift_consI]; exact c.look x B' hB'
  lookT x B h k' ρ τ1 τ2 h1 h2 b1 b2 := by
    rw [lookup_dshift, Option.map_eq_some_iff] at h
    obtain ⟨B', hB', rfl⟩ := h
    rw [dshift_subst, dshift_subst]
    have h1' := INear.tail h1; have h2' := INear.tail h2
    rw [cons_comp_tail] at h1' h2'
    exact c.lookT x B' hB' k' ρ τ1.tail τ2.tail h1' h2' b1 b2

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
  hγ y := by rw [← id_up, isub_dshift, c.hγ]
  hγ' y := by rw [← id_up, isub_dshift, c.hγ']
  face := by
    show I.Entails .one (Φ.shift.subst (I.up c.σ.τ))
    rw [I_shift_subst_up]; exact ent_shift c.face
  look x B h := by
    rw [lookup_dshift, Option.map_eq_some_iff] at h
    obtain ⟨B', hB', rfl⟩ := h
    show RE2 S (k + 1) (B'.dshift.subst (dupS c.γ) (I.up c.σ.τ)) (c.γ x).dshift (c.γ' x).dshift
    rw [dshift_dup_subst]; exact RE2.dshift hW (c.look x B' hB')
  lookT x B h k' ρ τ1 τ2 h1 h2 b1 b2 := by
    rw [lookup_dshift, Option.map_eq_some_iff] at h
    obtain ⟨B', hB', rfl⟩ := h
    have e : ∀ (b : Bool) (τ : ISub k' (Ψ + 1)),
        B'.dshift.subst (fun y => (cond b (fun x => (c.γ x).dshift) (fun x => (c.γ' x).dshift) y).isub ρ) τ.τ =
          B'.subst (fun y => (cond b c.γ c.γ' y).isub ρ.tail) τ.tail.τ := by
      intro b τ; rw [dshift_subst]
      congr 1; funext y; cases b <;> exact dshift_isub _ _
    rw [e, e]
    have h1' := INear.tail h1; have h2' := INear.tail h2
    rw [ISub.up_comp_tail] at h1' h2'
    exact c.lookT x B' hB' k' ρ.tail τ1.tail τ2.tail h1' h2' b1 b2

/-- Extending the face by a face that holds. -/
def cof (c : CSub2 S Ψ Φ Γ k) {φ : I} (h : I.Entails .one (φ.subst c.σ.τ)) :
    CSub2 S Ψ (KubusCore.cof Φ φ) Γ k :=
  { c with face := ent_and_intro c.face h }

/-- Restricting to a smaller face. -/
def restrictTo {Φ' : I} (he : I.Entails Φ' Φ) (c : CSub2 S Ψ Φ' Γ k) : CSub2 S Ψ Φ Γ k :=
  { c with face := ent_trans c.face (ent_subst he _) }

omit hW in
theorem cond_self_fun (b : Bool) (γ : ℕ → Tm) : cond b γ γ = γ := by cases b <;> rfl

/-- The left instance on both sides. -/
def diagL (c : CSub2 S Ψ Φ Γ k) : CSub2 S Ψ Φ Γ k where
  σ := c.σ
  σ' := c.σ
  hσ := INear.refl _
  γ := c.γ
  γ' := c.γ
  hγ := c.hγ
  hγ' := c.hγ
  face := c.face
  look x A h := (perK hW (c.tyCode_look hW h)).reflEl (c.lookT' h) (c.look x A h)
  lookT x A h k' ρ τ1 τ2 h1 h2 b1 b2 := by
    rw [cond_self_fun, cond_self_fun]
    exact c.lookT x A h k' ρ τ1 τ2 h1 h2 true true

/-- The right instance on both sides. -/
def diagR (c : CSub2 S Ψ Φ Γ k) : CSub2 S Ψ Φ Γ k where
  σ := c.σ'
  σ' := c.σ'
  hσ := INear.refl _
  γ := c.γ'
  γ' := c.γ'
  hγ := c.hγ'
  hγ' := c.hγ'
  face := c.face'
  look x A h := RE2.conv hW (c.lookT' h)
    ((perK hW (c.tyCode_look hW h)).reflEl' (c.lookT' h) (c.look x A h))
  lookT x A h k' ρ τ1 τ2 h1 h2 b1 b2 := by
    rw [cond_self_fun, cond_self_fun]
    exact c.lookT x A h k' ρ τ1 τ2 ((c.hσ.comp ρ).trans h1) ((c.hσ.comp ρ).trans h2) false false

omit hW in
theorem cond_cond (b b1 b2 : Bool) (γ γ' : ℕ → Tm) (ρ : ISub k' k) (y : ℕ) :
    cond b (fun x => (cond b1 γ γ' x).isub ρ) (fun x => (cond b2 γ γ' x).isub ρ) y =
      (cond (cond b b1 b2) γ γ' y).isub ρ := by
  cases b <;> rfl

/-- A variant of a related substitution: a restriction, with nearby interval substitutions and either
term substitution on each side. -/
def variant (c : CSub2 S Ψ Φ Γ k) (ρ : ISub k' k) (τ1 τ2 : ISub k' Ψ) (h1 : INear (c.σ.comp ρ) τ1)
    (h2 : INear (c.σ.comp ρ) τ2) (b1 b2 : Bool) : CSub2 S Ψ Φ Γ k' where
  σ := τ1
  σ' := τ2
  hσ := h1.symm.trans h2
  γ y := (cond b1 c.γ c.γ' y).isub ρ
  γ' y := (cond b2 c.γ c.γ' y).isub ρ
  hγ y := by rw [Tm.isub_isub, ISub.comp_id]
  hγ' y := by rw [Tm.isub_isub, ISub.comp_id]
  face := by
    have := ent_subst c.face ρ.τ
    rw [I_subst_subst] at this
    exact ent_trans this (eq_ent (I_eq_subst_congr h1 Φ))
  look x B h := by
    have hl := RE2.isub hW (c.look x B h) ρ
    rw [subst_isub2] at hl
    have hT := c.lookT x B h k' ρ (c.σ.comp ρ) τ1 (INear.refl _) h1 true b1
    have hTT := c.lookT x B h k' ρ τ1 τ1 h1 h1 b1 b1
    have hl' := RE2.conv hW hT hl
    cases b1 <;> cases b2
    · exact RE2.trans hW hTT (RE2.symm hW hTT hl') hl'
    · exact RE2.symm hW hTT hl'
    · exact hl'
    · exact RE2.trans hW hTT hl' (RE2.symm hW hTT hl')
  lookT x B h k'' ρ' τ1' τ2' h1' h2' b1' b2' := by
    have e : ∀ b : Bool, (fun y => (cond b (fun x => (cond b1 c.γ c.γ' x).isub ρ)
        (fun x => (cond b2 c.γ c.γ' x).isub ρ) y).isub ρ') =
        fun y => (cond (cond b b1 b2) c.γ c.γ' y).isub (ρ.comp ρ') := by
      intro b; funext y; rw [cond_cond, Tm.isub_isub]
    rw [e, e]
    have hn : INear (c.σ.comp (ρ.comp ρ')) (τ1.comp ρ') := by rw [← ISub.comp_assoc]; exact h1.comp ρ'
    exact c.lookT x B h k'' (ρ.comp ρ') τ1' τ2' (hn.trans h1') (hn.trans h2') _ _

/-- A type related at all related substitutions is robustly related. -/
theorem tyRob_of {A : Tm} (hA : ∀ k (c : CSub2 S Ψ Φ Γ k), RT2 S k (c.L A) (c.R A)) (c : CSub2 S Ψ Φ Γ k) :
    TyRob S A c.σ c.γ c.γ' :=
  fun k' ρ τ1 τ2 h1 h2 b1 b2 => hA k' (c.variant hW ρ τ1 τ2 h1 h2 b1 b2)

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
