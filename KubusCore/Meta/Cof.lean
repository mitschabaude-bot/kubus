import KubusCore.Meta.Subst

/-!
# Metatheory: cofibrations and interval equality

`I.Entails` is defined syntactically on disjunctive normal forms. Here it is characterized
semantically: `φ ⊨ ψ` iff every assignment of the variables into the three-element Kleene
algebra `{0, a, 1}` (a sub-algebra of `M4`) that makes `φ` true makes `ψ` true. From this,
entailment is stable under every interval substitution, `∀i. φ` (`I.forall0`) commutes with
substitution up to equivalence, and a face that entails `r = 1` makes `r` equal to `1` in the
free De Morgan algebra after substituting its endpoints.
-/

namespace KubusCore.Meta

open I I.M4

/-! ## `M4` facts -/

def isK3 (x : M4) : Prop := x ≠ .b

instance (x : M4) : Decidable (isK3 x) := inferInstanceAs (Decidable (x ≠ .b))

def K3Asg (ρ : Nat → M4) : Prop := ∀ i, isK3 (ρ i)

theorem meet_one_iff {x y : M4} : x.meet y = .one ↔ x = .one ∧ y = .one := by
  cases x <;> cases y <;> decide

theorem join_zero_iff {x y : M4} : x.join y = .zero ↔ x = .zero ∧ y = .zero := by
  cases x <;> cases y <;> decide

theorem neg_one_iff {x : M4} : x.neg = .one ↔ x = .zero := by cases x <;> decide

theorem neg_zero_iff {x : M4} : x.neg = .zero ↔ x = .one := by cases x <;> decide

theorem join_one_iff_k3 {x y : M4} (hx : isK3 x) (hy : isK3 y) :
    x.join y = .one ↔ x = .one ∨ y = .one := by
  unfold isK3 at *; cases x <;> cases y <;> simp_all <;> decide

theorem meet_zero_iff_k3 {x y : M4} (hx : isK3 x) (hy : isK3 y) :
    x.meet y = .zero ↔ x = .zero ∨ y = .zero := by
  unfold isK3 at *; cases x <;> cases y <;> simp_all <;> decide

theorem eval_k3 {ρ : Nat → M4} (hρ : K3Asg ρ) (r : I) : isK3 (r.eval ρ) := by
  induction r with
  | zero => simp [isK3, eval]
  | one => simp [isK3, eval]
  | var i => exact hρ i
  | neg r ih =>
    unfold isK3 at *; simp only [eval]; revert ih
    generalize r.eval ρ = x; cases x <;> decide
  | and r s ihr ihs | or r s ihr ihs =>
    unfold isK3 at *; revert ihr ihs; simp only [eval]
    generalize r.eval ρ = x; generalize s.eval ρ = y
    cases x <;> cases y <;> decide

theorem eval_subst (τ : Nat → I) (ρ : Nat → M4) (r : I) :
    (r.subst τ).eval ρ = r.eval (fun i => (τ i).eval ρ) := by
  induction r <;> simp_all [I.subst, eval]

theorem eval_ren (δ : Nat → Nat) (ρ : Nat → M4) (r : I) :
    (r.ren δ).eval ρ = r.eval (fun i => ρ (δ i)) := by
  rw [I.ren, eval_subst]; rfl

theorem eval_congr {ρ ρ' : Nat → M4} (h : ∀ i, ρ i = ρ' i) (r : I) : r.eval ρ = r.eval ρ' := by
  rw [funext h]

/-! ## Semantics of the face lattice -/

def litVal (d : Bool) : M4 := if d then .one else .zero

/-- An assignment satisfies a face. -/
def Sat (ρ : Nat → M4) (c : Face) : Prop := ∀ l ∈ c, ρ l.1 = litVal l.2

theorem sat_append {ρ : Nat → M4} {c d : Face} : Sat ρ (c ++ d) ↔ Sat ρ c ∧ Sat ρ d := by
  simp only [Sat, List.mem_append]
  constructor
  · intro h; exact ⟨fun l hl => h l (.inl hl), fun l hl => h l (.inr hl)⟩
  · rintro ⟨h1, h2⟩ l (hl | hl)
    · exact h1 l hl
    · exact h2 l hl

theorem consistent_iff {c : Face} : Face.consistent c = true ↔ ∀ l ∈ c, (l.1, !l.2) ∉ c := by
  simp only [Face.consistent, List.all_eq_true]
  constructor
  · intro h l hl hm
    have := h l hl
    rw [List.contains_iff_mem.2 hm] at this
    cases this
  · intro h l hl
    cases hcont : c.contains (l.1, !l.2)
    · rfl
    · exact absurd (List.contains_iff_mem.1 hcont) (h l hl)

theorem dnf_sem {ρ : Nat → M4} (hρ : K3Asg ρ) (r : I) :
    (r.eval ρ = .one ↔ ∃ c ∈ dnf true r, Sat ρ c) ∧
    (r.eval ρ = .zero ↔ ∃ c ∈ dnf false r, Sat ρ c) := by
  induction r with
  | zero => simp [dnf, eval, Sat]
  | one => simp [dnf, eval, Sat]
  | var i =>
    simp only [dnf, eval, List.mem_singleton, exists_eq_left, Sat, forall_eq, litVal]
    simp
  | neg r ih =>
    simp only [dnf, eval, Bool.not_true, Bool.not_false, neg_one_iff, neg_zero_iff]
    exact ⟨ih.2, ih.1⟩
  | and r s ihr ihs =>
    simp only [dnf, eval]
    constructor
    · rw [meet_one_iff, ihr.1, ihs.1]
      simp only [List.mem_flatMap, List.mem_map]
      constructor
      · rintro ⟨⟨c, hc, h1⟩, ⟨d, hd, h2⟩⟩
        exact ⟨c ++ d, ⟨c, hc, d, hd, rfl⟩, sat_append.2 ⟨h1, h2⟩⟩
      · rintro ⟨_, ⟨c, hc, d, hd, rfl⟩, h⟩
        exact ⟨⟨c, hc, (sat_append.1 h).1⟩, ⟨d, hd, (sat_append.1 h).2⟩⟩
    · rw [meet_zero_iff_k3 (eval_k3 hρ r) (eval_k3 hρ s), ihr.2, ihs.2]
      simp only [List.mem_append]
      constructor
      · rintro (⟨c, hc, h⟩ | ⟨c, hc, h⟩)
        · exact ⟨c, .inl hc, h⟩
        · exact ⟨c, .inr hc, h⟩
      · rintro ⟨c, hc | hc, h⟩
        · exact .inl ⟨c, hc, h⟩
        · exact .inr ⟨c, hc, h⟩
  | or r s ihr ihs =>
    simp only [dnf, eval]
    constructor
    · rw [join_one_iff_k3 (eval_k3 hρ r) (eval_k3 hρ s), ihr.1, ihs.1]
      simp only [List.mem_append]
      constructor
      · rintro (⟨c, hc, h⟩ | ⟨c, hc, h⟩)
        · exact ⟨c, .inl hc, h⟩
        · exact ⟨c, .inr hc, h⟩
      · rintro ⟨c, hc | hc, h⟩
        · exact .inl ⟨c, hc, h⟩
        · exact .inr ⟨c, hc, h⟩
    · rw [join_zero_iff, ihr.2, ihs.2]
      simp only [List.mem_flatMap, List.mem_map]
      constructor
      · rintro ⟨⟨c, hc, h1⟩, ⟨d, hd, h2⟩⟩
        exact ⟨c ++ d, ⟨c, hc, d, hd, rfl⟩, sat_append.2 ⟨h1, h2⟩⟩
      · rintro ⟨_, ⟨c, hc, d, hd, rfl⟩, h⟩
        exact ⟨⟨c, hc, (sat_append.1 h).1⟩, ⟨d, hd, (sat_append.1 h).2⟩⟩

theorem sat_consistent {ρ : Nat → M4} {c : Face} (h : Sat ρ c) : Face.consistent c = true := by
  simp only [Face.consistent, List.all_eq_true]
  intro l hl
  cases hcont : c.contains (l.1, !l.2)
  · rfl
  exfalso
  have hm := List.contains_iff_mem.1 hcont
  have h1 := h l hl
  have h2 := h _ hm
  rw [h1] at h2
  cases hd : l.2 <;> simp [litVal, hd] at h2

theorem faces_sem {ρ : Nat → M4} (hρ : K3Asg ρ) (r : I) :
    r.eval ρ = .one ↔ ∃ c ∈ r.faces, Sat ρ c := by
  rw [(dnf_sem hρ r).1]
  simp only [faces, List.mem_filter]
  constructor
  · rintro ⟨c, hc, h⟩; exact ⟨c, ⟨hc, sat_consistent h⟩, h⟩
  · rintro ⟨c, ⟨hc, _⟩, h⟩; exact ⟨c, hc, h⟩

/-- The canonical assignment of a consistent face: its literals, and `a` elsewhere. -/
def faceAsg (c : Face) (i : Nat) : M4 :=
  if c.contains (i, true) then .one else if c.contains (i, false) then .zero else .a

theorem faceAsg_k3 (c : Face) : K3Asg (faceAsg c) := by
  intro i; unfold faceAsg isK3; split
  · decide
  · split <;> decide

theorem faceAsg_sat {c : Face} (hc : Face.consistent c = true) : Sat (faceAsg c) c := by
  intro l hl
  obtain ⟨i, d⟩ := l
  simp only [Face.consistent, List.all_eq_true] at hc
  have := hc (i, d) hl
  have hn : (i, !d) ∉ c := consistent_iff.1 (by simpa [Face.consistent] using hc) (i, d) hl
  have hm : c.contains (i, d) = true := List.contains_iff_mem.2 hl
  have hn' : c.contains (i, !d) = false := by
    cases h3 : c.contains (i, !d)
    · rfl
    · exact absurd (List.contains_iff_mem.1 h3) hn
  cases d <;> simp_all [faceAsg, litVal]

theorem sat_faceAsg {c d : Face} (h : Sat (faceAsg c) d) : ∀ l ∈ d, l ∈ c := by
  intro l hl
  obtain ⟨i, e⟩ := l
  have := h _ hl
  simp only [faceAsg, litVal] at this
  cases e <;> split at this <;> (try split at this) <;> simp_all

/-- Entailment is semantic entailment over Kleene assignments. -/
theorem entails_iff {φ ψ : I} :
    I.Entails φ ψ ↔ ∀ ρ, K3Asg ρ → φ.eval ρ = .one → ψ.eval ρ = .one := by
  simp only [I.Entails, I.entails, List.all_eq_true, List.any_eq_true]
  constructor
  · intro h ρ hρ hφ
    obtain ⟨c, hc, hs⟩ := (faces_sem hρ φ).1 hφ
    obtain ⟨d, hd, hdc⟩ := h c hc
    refine (faces_sem hρ ψ).2 ⟨d, hd, fun l hl => hs l ?_⟩
    simpa using hdc l hl
  · intro h c hc
    have hcons : Face.consistent c = true := (List.mem_filter.1 hc).2
    have := h _ (faceAsg_k3 c) ((faces_sem (faceAsg_k3 c) φ).2 ⟨c, hc, faceAsg_sat hcons⟩)
    obtain ⟨d, hd, hs⟩ := (faces_sem (faceAsg_k3 c) ψ).1 this
    refine ⟨d, hd, fun l hl => ?_⟩
    simpa using sat_faceAsg hs l hl

/-! ## Entailment lemmas -/

theorem ent_refl (φ : I) : I.Entails φ φ := entails_iff.2 fun _ _ h => h

theorem ent_trans {φ ψ χ : I} (h1 : I.Entails φ ψ) (h2 : I.Entails ψ χ) : I.Entails φ χ :=
  entails_iff.2 fun ρ hρ h => entails_iff.1 h2 ρ hρ (entails_iff.1 h1 ρ hρ h)

theorem ent_one (φ : I) : I.Entails φ .one := entails_iff.2 fun _ _ _ => rfl

theorem ent_zero (φ : I) : I.Entails .zero φ := entails_iff.2 fun _ _ h => by cases h

theorem ent_and_left (φ ψ : I) : I.Entails (.and φ ψ) φ :=
  entails_iff.2 fun _ _ h => (meet_one_iff.1 h).1

theorem ent_and_right (φ ψ : I) : I.Entails (.and φ ψ) ψ :=
  entails_iff.2 fun _ _ h => (meet_one_iff.1 h).2

theorem ent_and_intro {Φ φ ψ : I} (h1 : I.Entails Φ φ) (h2 : I.Entails Φ ψ) :
    I.Entails Φ (.and φ ψ) :=
  entails_iff.2 fun ρ hρ h => meet_one_iff.2 ⟨entails_iff.1 h1 ρ hρ h, entails_iff.1 h2 ρ hρ h⟩

theorem ent_and_mono {Φ Φ' φ φ' : I} (h1 : I.Entails Φ Φ') (h2 : I.Entails φ φ') :
    I.Entails (.and Φ φ) (.and Φ' φ') :=
  ent_and_intro (ent_trans (ent_and_left _ _) h1) (ent_trans (ent_and_right _ _) h2)

theorem ent_or_left (φ ψ : I) : I.Entails φ (.or φ ψ) :=
  entails_iff.2 fun ρ hρ h => (join_one_iff_k3 (eval_k3 hρ φ) (eval_k3 hρ ψ)).2 (.inl h)

theorem ent_or_right (φ ψ : I) : I.Entails ψ (.or φ ψ) :=
  entails_iff.2 fun ρ hρ h => (join_one_iff_k3 (eval_k3 hρ φ) (eval_k3 hρ ψ)).2 (.inr h)

theorem ent_or_elim {φ ψ χ : I} (h1 : I.Entails φ χ) (h2 : I.Entails ψ χ) :
    I.Entails (.or φ ψ) χ :=
  entails_iff.2 fun ρ hρ h => by
    rcases (join_one_iff_k3 (eval_k3 hρ φ) (eval_k3 hρ ψ)).1 h with h | h
    · exact entails_iff.1 h1 ρ hρ h
    · exact entails_iff.1 h2 ρ hρ h

/-- Entailment is stable under interval substitution. -/
theorem ent_subst {φ ψ : I} (h : I.Entails φ ψ) (τ : Nat → I) :
    I.Entails (φ.subst τ) (ψ.subst τ) :=
  entails_iff.2 fun ρ hρ hφ => by
    rw [eval_subst] at *
    exact entails_iff.1 h _ (fun i => eval_k3 hρ (τ i)) hφ

theorem ent_ren {φ ψ : I} (h : I.Entails φ ψ) (δ : Nat → Nat) :
    I.Entails (φ.ren δ) (ψ.ren δ) := ent_subst h _

theorem ent_shift {φ ψ : I} (h : I.Entails φ ψ) : I.Entails φ.shift ψ.shift := ent_ren h _

theorem eq_ent {r s : I} (h : I.Eq r s) : I.Entails r s :=
  entails_iff.2 fun ρ _ hr => (h ρ) ▸ hr

theorem I_eq_symm {r s : I} (h : I.Eq r s) : I.Eq s r := fun ρ => (h ρ).symm

theorem I_eq_trans {r s t : I} (h1 : I.Eq r s) (h2 : I.Eq s t) : I.Eq r t := fun ρ => (h1 ρ).trans (h2 ρ)

theorem I_eq_refl (r : I) : I.Eq r r := fun _ => rfl

theorem I_eq_subst {r s : I} (h : I.Eq r s) (τ : Nat → I) : I.Eq (r.subst τ) (s.subst τ) :=
  fun ρ => by rw [eval_subst, eval_subst]; exact h _

/-- Pointwise equal substitutions give equal results. -/
theorem I_eq_subst_congr {τ τ' : Nat → I} (h : ∀ i, I.Eq (τ i) (τ' i)) (r : I) :
    I.Eq (r.subst τ) (r.subst τ') :=
  fun ρ => by rw [eval_subst, eval_subst]; exact eval_congr (fun i => h i ρ) r

/-! ## Scoping -/

theorem scoped_subst {r : I} {n m : Nat} (hr : r.Scoped n) {τ : Nat → I}
    (hτ : ∀ i < n, (τ i).Scoped m) : (r.subst τ).Scoped m := by
  induction r with
  | zero | one => trivial
  | var i => exact hτ i hr
  | neg r ih => exact ih hr
  | and r s ihr ihs | or r s ihr ihs => exact ⟨ihr hr.1, ihs hr.2⟩

theorem scoped_ren {r : I} {n m : Nat} (hr : r.Scoped n) {δ : Nat → Nat}
    (hδ : ∀ i < n, δ i < m) : (r.ren δ).Scoped m := scoped_subst hr hδ

theorem scoped_shift {r : I} {n : Nat} (hr : r.Scoped n) : r.shift.Scoped (n + 1) :=
  scoped_ren hr fun _ h => Nat.succ_lt_succ h

theorem scoped_mono {r : I} {n m : Nat} (hr : r.Scoped n) (h : n ≤ m) : r.Scoped m :=
  by simpa [I_ren_id] using scoped_ren (δ := id) hr fun i hi => Nat.lt_of_lt_of_le hi h

theorem subst_scoped_eq {r : I} {n : Nat} (hr : r.Scoped n) {τ τ' : Nat → I}
    (h : ∀ i < n, τ i = τ' i) : r.subst τ = r.subst τ' := by
  induction r with
  | zero | one => rfl
  | var i => exact h i hr
  | neg r ih => simp only [I.subst]; rw [ih hr]
  | and r s ihr ihs | or r s ihr ihs => simp only [I.subst]; rw [ihr hr.1, ihs hr.2]

theorem subst_scoped_id {r : I} {n : Nat} (hr : r.Scoped n) {τ : Nat → I}
    (h : ∀ i < n, τ i = .var i) : r.subst τ = r := by
  rw [subst_scoped_eq hr h, I_subst_var]

/-! ## `∀ i. φ` -/

/-- Extend an assignment by a value for variable 0. -/
def consAsg (x : M4) (ρ : Nat → M4) : Nat → M4
  | 0 => x
  | n + 1 => ρ n

theorem consAsg_k3 {x : M4} (hx : isK3 x) {ρ : Nat → M4} (hρ : K3Asg ρ) : K3Asg (consAsg x ρ) := by
  intro i; cases i
  · exact hx
  · exact hρ _

def clauseOK (ρ : Nat → M4) (c : Face) : Bool := c.all fun l => ρ l.1 == litVal l.2

theorem eval_ofFace (ρ : Nat → M4) (c : Face) :
    (I.ofFace c).eval ρ = .one ↔ Sat ρ c := by
  induction c with
  | nil => simp [I.ofFace, eval, Sat]
  | cons l c ih =>
    obtain ⟨i, d⟩ := l
    simp only [I.ofFace, List.foldr_cons] at *
    simp only [eval, meet_one_iff, ih]
    simp only [Sat, List.mem_cons, forall_eq_or_imp]
    apply and_congr_left'
    cases d <;> simp [I.lit, eval, litVal, neg_one_iff]

theorem eval_ofFaces {ρ : Nat → M4} (hρ : K3Asg ρ) (cs : List Face) :
    (I.ofFaces cs).eval ρ = .one ↔ ∃ c ∈ cs, Sat ρ c := by
  induction cs with
  | nil => simp [I.ofFaces, eval]
  | cons c cs ih =>
    simp only [I.ofFaces, List.foldr_cons] at *
    have hk : isK3 ((List.foldr (fun α r => I.or (I.ofFace α) r) I.zero cs).eval ρ) := eval_k3 hρ _
    rw [eval, join_one_iff_k3 (eval_k3 hρ _) hk, eval_ofFace, ih]
    simp

theorem forall0_sem {ρ : Nat → M4} (hρ : K3Asg ρ) (φ : I) :
    φ.forall0.eval ρ = .one ↔ φ.eval (consAsg .a ρ) = .one := by
  have hk : K3Asg (consAsg .a ρ) := consAsg_k3 (by decide) hρ
  rw [I.forall0, eval_ofFaces hρ, faces_sem hk]
  simp only [List.mem_map, List.mem_filter, List.all_eq_true]
  constructor
  · rintro ⟨_, ⟨c, ⟨hc, hnz⟩, rfl⟩, hs⟩
    refine ⟨c, hc, fun l hl => ?_⟩
    have hl0 := hnz l hl
    have := hs _ (List.mem_map.2 ⟨l, hl, rfl⟩)
    obtain ⟨i, d⟩ := l
    cases i with
    | zero => simp at hl0
    | succ n => simpa [consAsg] using this
  · rintro ⟨c, hc, hs⟩
    have hnz : ∀ l ∈ c, (l.1 != 0) = true := by
      intro l hl
      have := hs l hl
      obtain ⟨i, d⟩ := l
      cases i with
      | zero => cases d <;> simp [consAsg, litVal] at this
      | succ n => simp
    refine ⟨_, ⟨c, ⟨hc, hnz⟩, rfl⟩, ?_⟩
    intro l hl
    obtain ⟨⟨i, d⟩, hl', rfl⟩ := List.mem_map.1 hl
    have := hs _ hl'
    cases i with
    | zero => simpa using hnz _ hl'
    | succ n => simpa [consAsg] using this

theorem eval_up (τ : Nat → I) (x : M4) (ρ : Nat → M4) (i : Nat) :
    (I.up τ i).eval (consAsg x ρ) = consAsg x (fun j => (τ j).eval ρ) i := by
  cases i with
  | zero => rfl
  | succ n => simp only [I.up, I.shift, eval_ren]; rfl

/-- `(∀i. φ)τ` and `∀i. (φ τ⁺)` are equivalent. -/
theorem forall0_subst (φ : I) (τ : Nat → I) :
    I.Entails (φ.forall0.subst τ) (φ.subst (I.up τ)).forall0 ∧
    I.Entails (φ.subst (I.up τ)).forall0 (φ.forall0.subst τ) := by
  have key : ∀ ρ, K3Asg ρ →
      ((φ.forall0.subst τ).eval ρ = .one ↔ (φ.subst (I.up τ)).forall0.eval ρ = .one) := by
    intro ρ hρ
    rw [eval_subst, forall0_sem (fun i => eval_k3 hρ (τ i)), forall0_sem hρ, eval_subst]
    rw [eval_congr (eval_up τ .a ρ)]
  exact ⟨entails_iff.2 fun ρ hρ h => (key ρ hρ).1 h, entails_iff.2 fun ρ hρ h => (key ρ hρ).2 h⟩

/-! ## Faces as substitutions -/

/-- The substitution setting the variables of a face to their endpoints. -/
def faceSub : Face → Nat → I
  | [], i => .var i
  | (k, d) :: c, i => if i = k then I.ofDir d else faceSub c i

theorem eval_ofDir (d : Bool) (ρ : Nat → M4) : (I.ofDir d).eval ρ = litVal d := by
  cases d <;> rfl

/-- On an assignment satisfying a consistent face, substituting the face changes nothing. -/
theorem eval_faceSub {ρ : Nat → M4} {c : Face} (h : Sat ρ c) (i : Nat) :
    (faceSub c i).eval ρ = ρ i := by
  induction c with
  | nil => rfl
  | cons l c ih =>
    obtain ⟨k, d⟩ := l
    simp only [faceSub]
    split
    · subst i; rw [eval_ofDir]; exact (h _ (List.mem_cons_self ..)).symm
    · exact ih fun l hl => h l (List.mem_cons_of_mem _ hl)

/-- Substituting the face gives an assignment satisfying it. -/
theorem sat_faceSub {c : Face} (hc : Face.consistent c = true) (ρ : Nat → M4) :
    Sat (fun i => (faceSub c i).eval ρ) c := by
  intro l hl
  induction c with
  | nil => cases hl
  | cons l' c ih =>
    obtain ⟨k, d⟩ := l'
    simp only [faceSub]
    rcases List.mem_cons.1 hl with rfl | hl'
    · simp [eval_ofDir]
    · split
      · rename_i h
        -- `l = (k, e)` with `(k, d)` earlier: by consistency `e = d`
        obtain ⟨i, e⟩ := l
        simp only at h; subst h
        have hn := consistent_iff.1 hc (i, e) hl
        cases d <;> cases e <;> simp_all [eval_ofDir]
      · have hc' : Face.consistent c = true := by
          refine consistent_iff.2 fun x hx hm => ?_
          exact consistent_iff.1 hc x (List.mem_cons_of_mem _ hx) (List.mem_cons_of_mem _ hm)
        exact ih hc' hl'

/-- The four-element algebra with `a` and `b` swapped: an automorphism. -/
def swap : M4 → M4
  | .zero => .zero | .a => .b | .b => .a | .one => .one

theorem eval_swap (ρ : Nat → M4) (r : I) : r.eval (fun i => swap (ρ i)) = swap (r.eval ρ) := by
  induction r with
  | zero | one => rfl
  | var i => rfl
  | neg r ih => simp only [eval, ih]; cases r.eval ρ <;> rfl
  | and r s ihr ihs | or r s ihr ihs =>
    simp only [eval, ihr, ihs]; cases r.eval ρ <;> cases s.eval ρ <;> rfl

def lo1 (x : M4) : Bool := x.toPair.1
def lo2 (x : M4) : Bool := x.toPair.2

theorem lo1_meet (x y : M4) : lo1 (x.meet y) = (lo1 x && lo1 y) := by cases x <;> cases y <;> rfl
theorem lo2_meet (x y : M4) : lo2 (x.meet y) = (lo2 x && lo2 y) := by cases x <;> cases y <;> rfl
theorem lo1_join (x y : M4) : lo1 (x.join y) = (lo1 x || lo1 y) := by cases x <;> cases y <;> rfl
theorem lo2_join (x y : M4) : lo2 (x.join y) = (lo2 x || lo2 y) := by cases x <;> cases y <;> rfl
theorem lo1_neg (x : M4) : lo1 x.neg = !lo2 x := by cases x <;> rfl
theorem lo2_neg (x : M4) : lo2 x.neg = !lo1 x := by cases x <;> rfl

theorem band_mono {a b c d : Bool} (h1 : a ≤ b) (h2 : c ≤ d) : (a && c) ≤ (b && d) := by
  revert h1 h2; cases a <;> cases b <;> cases c <;> cases d <;> decide
theorem bor_mono {a b c d : Bool} (h1 : a ≤ b) (h2 : c ≤ d) : (a || c) ≤ (b || d) := by
  revert h1 h2; cases a <;> cases b <;> cases c <;> cases d <;> decide
theorem bnot_anti {a b : Bool} (h1 : a ≤ b) : (!b) ≤ (!a) := by
  revert h1; cases a <;> cases b <;> decide

/-- Bounds: the all-`b` assignment minimizes the first component and maximizes the second;
the all-`a` assignment does the opposite. -/
theorem eval_bounds (r : I) (ρ : Nat → M4) :
    (lo1 (r.eval fun _ => .b) ≤ lo1 (r.eval ρ) ∧ lo1 (r.eval ρ) ≤ lo1 (r.eval fun _ => .a)) ∧
    (lo2 (r.eval fun _ => .a) ≤ lo2 (r.eval ρ) ∧ lo2 (r.eval ρ) ≤ lo2 (r.eval fun _ => .b)) := by
  induction r with
  | zero | one => simp [eval]
  | var i => simp only [eval]; generalize ρ i = x; cases x <;> decide
  | neg r ih =>
    simp only [eval, lo1_neg, lo2_neg]
    exact ⟨⟨bnot_anti ih.2.2, bnot_anti ih.2.1⟩, ⟨bnot_anti ih.1.2, bnot_anti ih.1.1⟩⟩
  | and r s ihr ihs =>
    simp only [eval, lo1_meet, lo2_meet]
    exact ⟨⟨band_mono ihr.1.1 ihs.1.1, band_mono ihr.1.2 ihs.1.2⟩,
      ⟨band_mono ihr.2.1 ihs.2.1, band_mono ihr.2.2 ihs.2.2⟩⟩
  | or r s ihr ihs =>
    simp only [eval, lo1_join, lo2_join]
    exact ⟨⟨bor_mono ihr.1.1 ihs.1.1, bor_mono ihr.1.2 ihs.1.2⟩,
      ⟨bor_mono ihr.2.1 ihs.2.1, bor_mono ihr.2.2 ihs.2.2⟩⟩

/-- A Kleene tautology is a De Morgan tautology. -/
theorem taut_of_k3 {r : I} (h : ∀ ρ, K3Asg ρ → r.eval ρ = .one) : I.Eq r .one := by
  intro ρ
  have ha := h (fun _ => .a) (fun _ => (by decide : (M4.a) ≠ M4.b))
  have hb : r.eval (fun _ => .b) = .one := by
    have := eval_swap (fun _ => .a) r
    simp only [swap] at this
    rw [this, ha]
  have hbd := eval_bounds r ρ
  rw [ha, hb] at hbd
  simp only [eval]
  revert hbd
  generalize r.eval ρ = x
  cases x <;> decide

/-- Under a face entailing `r`, `r` becomes `1` after substituting the face. -/
theorem faceSub_eq_one {c : Face} (hc : Face.consistent c = true) {r : I}
    (h : I.Entails (I.ofFace c) r) : I.Eq (r.subst (faceSub c)) .one := by
  apply taut_of_k3
  intro ρ hρ
  rw [eval_subst]
  apply entails_iff.1 h _ (fun i => eval_k3 hρ _)
  exact (eval_ofFace _ c).2 (sat_faceSub hc ρ)

theorem faceSub_eq_zero {c : Face} (hc : Face.consistent c = true) {r : I}
    (h : I.Entails (I.ofFace c) (.neg r)) : I.Eq (r.subst (faceSub c)) .zero := by
  have := faceSub_eq_one hc h
  intro ρ
  have h1 := this ρ
  simp only [I.subst, eval] at h1
  exact neg_one_iff.1 h1

/-- A cofibration is covered by its faces. -/
theorem ent_ofFaces (Φ : I) : I.Entails Φ (I.ofFaces Φ.faces) :=
  entails_iff.2 fun ρ hρ h => (eval_ofFaces hρ _).2 ((faces_sem hρ Φ).1 h)

theorem ofFace_ent {Φ : I} {c : Face} (hc : c ∈ Φ.faces) : I.Entails (I.ofFace c) Φ :=
  entails_iff.2 fun ρ hρ h => (faces_sem hρ Φ).2 ⟨c, hc, (eval_ofFace ρ c).1 h⟩

theorem ofFace_ent_lit {c : Face} {k : Nat} {d : Bool} (h : (k, d) ∈ c) :
    I.Entails (I.ofFace c) (I.lit k d) :=
  entails_iff.2 fun ρ _ hs => by
    have := (eval_ofFace ρ c).1 hs _ h
    cases d <;> simp_all [I.lit, eval, litVal] <;> rfl

theorem faces_consistent {Φ : I} {c : Face} (hc : c ∈ Φ.faces) : Face.consistent c = true :=
  (List.mem_filter.1 hc).2

theorem scoped_ofFace {c : Face} {n : Nat} (h : ∀ l ∈ c, l.1 < n) : (I.ofFace c).Scoped n := by
  induction c with
  | nil => trivial
  | cons l c ih =>
    obtain ⟨i, d⟩ := l
    simp only [I.ofFace, List.foldr_cons] at *
    refine ⟨?_, ih fun l hl => h l (List.mem_cons_of_mem _ hl)⟩
    have := h _ (List.mem_cons_self ..)
    cases d <;> exact this

theorem scoped_ofFaces {cs : List Face} {n : Nat} (h : ∀ c ∈ cs, ∀ l ∈ c, l.1 < n) :
    (I.ofFaces cs).Scoped n := by
  induction cs with
  | nil => trivial
  | cons c cs ih =>
    simp only [I.ofFaces, List.foldr_cons] at *
    exact ⟨scoped_ofFace (h c (List.mem_cons_self ..)), ih fun c hc => h c (List.mem_cons_of_mem _ hc)⟩

theorem dnf_scoped {r : I} {m : Nat} (hr : r.Scoped m) :
    ∀ pos, ∀ c ∈ dnf pos r, ∀ l ∈ c, l.1 < m := by
  induction r with
  | zero => intro pos; cases pos <;> simp [dnf]
  | one => intro pos; cases pos <;> simp [dnf]
  | var i => intro pos c hc l hl; simp [dnf] at hc; subst hc; simp at hl; subst hl; exact hr
  | neg r ih => intro pos; cases pos <;> simpa [dnf] using ih hr _
  | and r s ihr ihs | or r s ihr ihs =>
    intro pos; cases pos <;> intro c hc l hl <;>
      simp only [dnf, List.mem_append, List.mem_flatMap, List.mem_map] at hc
    all_goals first
      | (rcases hc with hc | hc
         · exact ihr hr.1 _ c hc l hl
         · exact ihs hr.2 _ c hc l hl)
      | (obtain ⟨c1, hc1, c2, hc2, rfl⟩ := hc
         rcases List.mem_append.1 hl with hl | hl
         · exact ihr hr.1 _ c1 hc1 l hl
         · exact ihs hr.2 _ c2 hc2 l hl)

theorem faces_scoped {r : I} {m : Nat} (hr : r.Scoped m) : ∀ c ∈ r.faces, ∀ l ∈ c, l.1 < m :=
  fun c hc => dnf_scoped hr true c (List.mem_filter.1 hc).1

end KubusCore.Meta
