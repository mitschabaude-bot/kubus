import KubusCore.Rules

/-!
# Kernel: syntactic lemmas and decision procedures

Everything here is about the syntax of `KubusCore` only: renaming fusion, closed terms,
scoping, and a decision procedure for equality of interval terms (`I.Eq`).
-/

namespace KubusCore

/-! ## Interval terms -/

namespace I

theorem subst_subst (σ τ : Nat → I) (r : I) :
    (r.subst σ).subst τ = r.subst fun i => (σ i).subst τ := by
  induction r <;> simp_all [subst]

theorem ren_ren (ρ ρ' : Nat → Nat) (r : I) : (r.ren ρ).ren ρ' = r.ren (ρ' ∘ ρ) := by
  simp only [ren, subst_subst]; rfl


theorem ren_id_of_scoped (δ : Nat → Nat) (r : I) (m : Nat) (hs : r.Scoped m)
    (h : ∀ i < m, δ i = i) : r.ren δ = r := by
  induction r with
  | zero | one => rfl
  | var i => simp [ren, subst, h i hs]
  | neg r ih => simp only [ren, subst] at *; rw [ih hs]
  | and r s ihr ihs | or r s ihr ihs =>
    simp only [ren, subst, Scoped] at *; rw [ihr hs.1, ihs hs.2]

theorem scoped_ren (δ : Nat → Nat) (r : I) (n m : Nat) (hs : r.Scoped n)
    (h : ∀ i < n, δ i < m) : (r.ren δ).Scoped m := by
  induction r with
  | zero | one => trivial
  | var i => exact h i hs
  | neg r ih => exact ih hs
  | and r s ihr ihs | or r s ihr ihs => exact ⟨ihr hs.1, ihs hs.2⟩

theorem scoped_shift {r : I} {n : Nat} (h : r.Scoped n) : r.shift.Scoped (n + 1) :=
  scoped_ren _ r n (n + 1) h fun _ hi => Nat.succ_lt_succ hi

theorem entails_one (φ : I) : Entails φ .one := by
  simp [Entails, entails, faces, dnf, Face.consistent]

/-! ### Entailment facts -/
theorem Face.consistent_append_left {c d : Face} (h : Face.consistent (c ++ d) = true) :
    Face.consistent c = true := by
  simp only [Face.consistent, List.all_eq_true] at *
  intro x hx
  have := h x (List.mem_append_left d hx)
  cases hc : List.contains _ (x.fst, !x.snd)
  · rfl
  · rw [List.contains_iff_mem.mpr (List.mem_append_left d (List.contains_iff_mem.mp hc))] at this
    cases this

theorem Face.consistent_append_right {c d : Face} (h : Face.consistent (c ++ d) = true) :
    Face.consistent d = true := by
  simp only [Face.consistent, List.all_eq_true] at *
  intro x hx
  have := h x (List.mem_append_right c hx)
  cases hc : List.contains _ (x.fst, !x.snd)
  · rfl
  · rw [List.contains_iff_mem.mpr (List.mem_append_right c (List.contains_iff_mem.mp hc))] at this
    cases this

theorem entails_and_left (Φ φ : I) : Entails (.and Φ φ) Φ := by
  simp only [Entails, entails, faces, dnf, List.all_eq_true, List.any_eq_true, List.mem_filter,
    List.mem_flatMap, List.mem_map]
  rintro x ⟨⟨c, hc, c', _, rfl⟩, hcons⟩
  refine ⟨c, ⟨hc, Face.consistent_append_left hcons⟩, ?_⟩
  simp only [List.contains_iff_mem]
  intro y hy; exact List.mem_append_left _ hy

theorem entails_and_right (Φ φ : I) : Entails (.and Φ φ) φ := by
  simp only [Entails, entails, faces, dnf, List.all_eq_true, List.any_eq_true, List.mem_filter,
    List.mem_flatMap, List.mem_map]
  rintro x ⟨⟨c, _, c', hc', rfl⟩, hcons⟩
  refine ⟨c', ⟨hc', Face.consistent_append_right hcons⟩, ?_⟩
  simp only [List.contains_iff_mem]
  intro y hy; exact List.mem_append_right _ hy

theorem entails_refl (φ : I) : Entails φ φ := by
  simp only [Entails, entails, List.all_eq_true, List.any_eq_true]
  intro c hc
  exact ⟨c, hc, by simp⟩

/-! ### Deciding `I.Eq` by enumerating assignments of the variables that occur -/

def vars : I → List Nat
  | zero | one => []
  | var i => [i]
  | neg r => r.vars
  | and r s | or r s => r.vars ++ s.vars

theorem eval_congr (r : I) (ρ ρ' : Nat → M4) (h : ∀ i ∈ r.vars, ρ i = ρ' i) :
    r.eval ρ = r.eval ρ' := by
  induction r with
  | zero | one => rfl
  | var i => exact h i (by simp [vars])
  | neg r ih => simp only [eval]; rw [ih h]
  | and r s ihr ihs | or r s ihr ihs =>
    simp only [eval]
    rw [ihr fun i hi => h i (by simp [vars, hi]), ihs fun i hi => h i (by simp [vars, hi])]

def allM4 : List M4 := [.zero, .a, .b, .one]

theorem mem_allM4 (m : M4) : m ∈ allM4 := by cases m <;> simp [allM4]

/-- All assignments of the variables `vs` (others are sent to `0`). -/
def assigns : List Nat → List (Nat → M4)
  | [] => [fun _ => .zero]
  | v :: vs => (assigns vs).flatMap fun σ => allM4.map fun m => fun x => if x = v then m else σ x

theorem assigns_complete (vs : List Nat) (ρ : Nat → M4) :
    ∃ σ ∈ assigns vs, ∀ v ∈ vs, σ v = ρ v := by
  induction vs with
  | nil => exact ⟨fun _ => .zero, by simp [assigns], by simp⟩
  | cons v vs ih =>
    obtain ⟨σ, hσ, h⟩ := ih
    refine ⟨fun x => if x = v then ρ v else σ x, ?_, ?_⟩
    · simp only [assigns, List.mem_flatMap, List.mem_map]
      exact ⟨σ, hσ, ρ v, mem_allM4 _, rfl⟩
    · intro w hw
      by_cases hwv : w = v
      · simp [hwv]
      · simp only [hwv, if_false]
        exact h w (by simpa [hwv] using hw)

def eqB (r s : I) : Bool := (assigns (r.vars ++ s.vars)).all fun σ => r.eval σ == s.eval σ

theorem eqB_sound {r s : I} (h : eqB r s = true) : I.Eq r s := by
  intro ρ
  obtain ⟨σ, hσ, hag⟩ := assigns_complete (r.vars ++ s.vars) ρ
  have := List.all_eq_true.mp h σ hσ
  have e : r.eval σ = s.eval σ := by simpa using this
  rw [← eval_congr r σ ρ (fun i hi => hag i (by simp [hi])),
      ← eval_congr s σ ρ (fun i hi => hag i (by simp [hi]))]
  exact e

end I

/-! ## Terms: renaming -/

namespace Tm

theorem upRen_comp (ρ ρ' : Nat → Nat) : upRen ρ' ∘ upRen ρ = upRen (ρ' ∘ ρ) := by
  funext n; cases n <;> rfl

theorem ren_ren (t : Tm) : ∀ (ρ δ ρ' δ' : Nat → Nat),
    (t.ren ρ δ).ren ρ' δ' = t.ren (ρ' ∘ ρ) (δ' ∘ δ) := by
  induction t <;> intros <;> simp_all [ren, I.ren_ren, upRen_comp]

theorem shift_dshift (t : Tm) : t.shift.dshift = t.dshift.shift := by
  simp only [shift, dshift, ren_ren]; rfl

theorem upRen_fix (ρ : Nat → Nat) (n : Nat) (h : ∀ x < n, ρ x = x) :
    ∀ x < n + 1, upRen ρ x = x := by
  intro x hx
  cases x with
  | zero => rfl
  | succ x => simp [upRen, h x (by omega)]

theorem ren_closed (t : Tm) : ∀ (n m : Nat) (ρ δ : Nat → Nat), t.closedB n m = true →
    (∀ x < n, ρ x = x) → (∀ i < m, δ i = i) → t.ren ρ δ = t := by
  induction t with
  | var x => intro n m ρ δ h hρ _; simp [closedB] at h; simp [ren, hρ x h]
  | const | univ | abort => intros; rfl
  | pi A B ihA ihB | sigma A B ihA ihB =>
    intro n m ρ δ h hρ hδ; simp only [closedB, Bool.and_eq_true] at h
    simp only [ren]; rw [ihA n m ρ δ h.1 hρ hδ, ihB (n + 1) m _ δ h.2 (upRen_fix ρ n hρ) hδ]
  | lam A t ihA ih =>
    intro n m ρ δ h hρ hδ; simp only [closedB, Bool.and_eq_true] at h
    simp only [ren]; rw [ihA n m ρ δ h.1 hρ hδ, ih (n + 1) m _ δ h.2 (upRen_fix ρ n hρ) hδ]
  | app f a ihf iha | pair f a ihf iha =>
    intro n m ρ δ h hρ hδ; simp only [closedB, Bool.and_eq_true] at h
    simp only [ren]; rw [ihf n m ρ δ h.1 hρ hδ, iha n m ρ δ h.2 hρ hδ]
  | fst p ih | snd p ih =>
    intro n m ρ δ h hρ hδ; simp only [closedB] at h
    simp only [ren]; rw [ih n m ρ δ h hρ hδ]
  | path A a b ihA iha ihb =>
    intro n m ρ δ h hρ hδ; simp only [closedB, Bool.and_eq_true] at h
    simp only [ren]
    rw [ihA n (m + 1) ρ _ h.1.1 hρ (upRen_fix δ m hδ), iha n m ρ δ h.1.2 hρ hδ,
      ihb n m ρ δ h.2 hρ hδ]
  | plam t ih | ipi t ih =>
    intro n m ρ δ h hρ hδ; simp only [closedB] at h
    simp only [ren]; rw [ih n (m + 1) ρ _ h hρ (upRen_fix δ m hδ)]
  | papp p r ih =>
    intro n m ρ δ h hρ hδ; simp only [closedB, Bool.and_eq_true] at h
    simp only [ren]
    rw [ih n m ρ δ h.1 hρ hδ, I.ren_id_of_scoped δ r m ((I.scopedB_iff _ _).mp h.2) hδ]
  | split φ t ψ u iht ihu =>
    intro n m ρ δ h hρ hδ; simp only [closedB, Bool.and_eq_true] at h
    simp only [ren]
    rw [I.ren_id_of_scoped δ φ m ((I.scopedB_iff _ _).mp h.1.1.1) hδ, iht n m ρ δ h.1.1.2 hρ hδ,
      I.ren_id_of_scoped δ ψ m ((I.scopedB_iff _ _).mp h.1.2) hδ, ihu n m ρ δ h.2 hρ hδ]
  | transp A φ a ihA iha =>
    intro n m ρ δ h hρ hδ; simp only [closedB, Bool.and_eq_true] at h
    simp only [ren]
    rw [ihA n (m + 1) ρ _ h.1.1 hρ (upRen_fix δ m hδ),
      I.ren_id_of_scoped δ φ m ((I.scopedB_iff _ _).mp h.1.2) hδ, iha n m ρ δ h.2 hρ hδ]
  | hcomp A φ u a ihA ihu iha =>
    intro n m ρ δ h hρ hδ; simp only [closedB, Bool.and_eq_true] at h
    simp only [ren]
    rw [ihA n m ρ δ h.1.1.1 hρ hδ, I.ren_id_of_scoped δ φ m ((I.scopedB_iff _ _).mp h.1.1.2) hδ,
      ihu n (m + 1) ρ _ h.1.2 hρ (upRen_fix δ m hδ), iha n m ρ δ h.2 hρ hδ]
  | glue A φ T e ihA ihT ihe =>
    intro n m ρ δ h hρ hδ; simp only [closedB, Bool.and_eq_true] at h
    simp only [ren]
    rw [ihA n m ρ δ h.1.1.1 hρ hδ, I.ren_id_of_scoped δ φ m ((I.scopedB_iff _ _).mp h.1.1.2) hδ,
      ihT n m ρ δ h.1.2 hρ hδ, ihe n m ρ δ h.2 hρ hδ]
  | glueEl φ e t a ihe iht iha =>
    intro n m ρ δ h hρ hδ; simp only [closedB, Bool.and_eq_true] at h
    simp only [ren]
    rw [I.ren_id_of_scoped δ φ m ((I.scopedB_iff _ _).mp h.1.1.1) hδ, ihe n m ρ δ h.1.1.2 hρ hδ,
      iht n m ρ δ h.1.2 hρ hδ, iha n m ρ δ h.2 hρ hδ]
  | unglue φ e g ihe ih =>
    intro n m ρ δ h hρ hδ; simp only [closedB, Bool.and_eq_true] at h
    simp only [ren]
    rw [I.ren_id_of_scoped δ φ m ((I.scopedB_iff _ _).mp h.1.1) hδ, ihe n m ρ δ h.1.2 hρ hδ,
      ih n m ρ δ h.2 hρ hδ]
  | tnil => intros; rfl
  | tcons t ts iht ihts =>
    intro n m ρ δ h hρ hδ; simp only [closedB, Bool.and_eq_true] at h
    simp only [ren]; rw [iht n m ρ δ h.1 hρ hδ, ihts n m ρ δ h.2 hρ hδ]
  | data d ps ih =>
    intro n m ρ δ h hρ hδ; simp only [closedB] at h
    simp only [ren]; rw [ih n m ρ δ h hρ hδ]
  | con d c ps args rs ihps iha =>
    intro n m ρ δ h hρ hδ; simp only [closedB, Bool.and_eq_true] at h
    have hrs : rs.map (·.ren δ) = rs := by
      conv => rhs; rw [← List.map_id rs]
      apply List.map_congr_left
      intro r hr
      exact I.ren_id_of_scoped δ r m ((I.scopedB_iff _ _).mp (List.all_eq_true.mp h.2 r hr)) hδ
    simp only [ren]; rw [ihps n m ρ δ h.1.1 hρ hδ, iha n m ρ δ h.1.2 hρ hδ, hrs]
  | elim d ps P bs t ihps ihP ihbs iht =>
    intro n m ρ δ h hρ hδ; simp only [closedB, Bool.and_eq_true] at h
    simp only [ren]
    rw [ihps n m ρ δ h.1.1.1 hρ hδ, ihP (n + 1) m _ δ h.1.1.2 (upRen_fix ρ n hρ) hδ,
      ihbs n m ρ δ h.1.2 hρ hδ, iht n m ρ δ h.2 hρ hδ]

theorem shift_closed {t : Tm} (h : t.closedB 0 0 = true) : t.shift = t :=
  ren_closed t 0 0 _ _ h (fun _ h => absurd h (Nat.not_lt_zero _)) (fun _ _ => rfl)

theorem dshift_closed {t : Tm} (h : t.closedB 0 0 = true) : t.dshift = t :=
  ren_closed t 0 0 _ _ h (fun _ _ => rfl) (fun _ h => absurd h (Nat.not_lt_zero _))

/-- Whether interval variable `i` occurs in `t` (free). -/
def mentionsI (i : Nat) : Tm → Bool
  | var _ | const _ | univ _ | abort => false
  | pi A B | sigma A B | app A B | pair A B | lam A B => A.mentionsI i || B.mentionsI i
  | fst t | snd t => t.mentionsI i
  | path A a b => A.mentionsI (i + 1) || a.mentionsI i || b.mentionsI i
  | plam t | ipi t => t.mentionsI (i + 1)
  | papp p r => p.mentionsI i || r.vars.contains i
  | split φ t ψ u => φ.vars.contains i || t.mentionsI i || ψ.vars.contains i || u.mentionsI i
  | transp A φ a => A.mentionsI (i + 1) || φ.vars.contains i || a.mentionsI i
  | tnil => false
  | tcons t ts => t.mentionsI i || ts.mentionsI i
  | data _ ps => ps.mentionsI i
  | con _ _ ps args rs => ps.mentionsI i || args.mentionsI i || rs.any (·.vars.contains i)
  | elim _ ps P bs t => ps.mentionsI i || P.mentionsI i || bs.mentionsI i || t.mentionsI i
  | hcomp A φ u a => A.mentionsI i || φ.vars.contains i || u.mentionsI (i + 1) || a.mentionsI i
  | glue A φ T e => A.mentionsI i || φ.vars.contains i || T.mentionsI i || e.mentionsI i
  | glueEl φ e t a => φ.vars.contains i || e.mentionsI i || t.mentionsI i || a.mentionsI i
  | unglue φ e g => φ.vars.contains i || e.mentionsI i || g.mentionsI i

end Tm

/-! ## Substitution after renaming -/

theorem I.subst_var (r : I) : r.subst I.var = r := by
  induction r <;> simp_all [I.subst]

theorem I.ren_subst (ρ : Nat → Nat) (σ : Nat → I) (r : I) : (r.ren ρ).subst σ = r.subst (σ ∘ ρ) := by
  simp only [I.ren, I.subst_subst]; rfl

namespace Tm

theorem up_upRen (σ : Nat → Tm) (ρ : Nat → Nat) : up σ ∘ upRen ρ = up (σ ∘ ρ) := by
  funext n; cases n <;> rfl

theorem Iup_upRen (τ : Nat → I) (δ : Nat → Nat) : I.up τ ∘ upRen δ = I.up (τ ∘ δ) := by
  funext n; cases n <;> rfl

theorem ren_subst (t : Tm) : ∀ (ρ δ : Nat → Nat) (σ : Nat → Tm) (τ : Nat → I),
    (t.ren ρ δ).subst σ τ = t.subst (σ ∘ ρ) (τ ∘ δ) := by
  induction t <;> intros <;> simp_all [ren, subst, I.ren_subst, up_upRen, Iup_upRen] <;> rfl

theorem up_var : up Tm.var = Tm.var := by funext n; cases n <;> rfl
theorem Iup_var : I.up I.var = I.var := by funext n; cases n <;> rfl
theorem dshift_var : (fun n => (Tm.var n).dshift) = Tm.var := rfl

theorem subst_id (t : Tm) : t.subst Tm.var I.var = t := by
  induction t <;> simp_all [subst, up_var, Iup_var, dshift_var, I.subst_var]

theorem subst_id' (t : Tm) (σ : Nat → Tm) (τ : Nat → I) (hσ : ∀ n, σ n = Tm.var n)
    (hτ : ∀ n, τ n = I.var n) : t.subst σ τ = t := by
  have h1 : σ = Tm.var := funext hσ
  have h2 : τ = I.var := funext hτ
  subst h1; subst h2; exact subst_id t

theorem dshift_dinst (t : Tm) (r : I) : t.dshift.dinst r = t := by
  simp only [dinst, dsubst, dshift, ren_subst]
  exact subst_id t

theorem shift_inst (t a : Tm) : t.shift.inst a = t := by
  simp only [inst, shift, ren_subst]
  exact subst_id t

theorem upShift_inst0 (B : Tm) : (B.ren (upRen Nat.succ) id).inst (.var 0) = B := by
  simp only [inst, ren_subst]
  exact subst_id' _ _ _ (fun n => by cases n <;> rfl) (fun n => rfl)

theorem upDShift_dinst0 (A : Tm) : (A.ren id (upRen Nat.succ)).dinst (.var 0) = A := by
  simp only [dinst, dsubst, ren_subst]
  exact subst_id' _ _ _ (fun n => rfl) (fun n => by cases n <;> rfl)

end Tm

/-! ## Contexts -/

theorem Ctx.lookup_dshift (Γ : Ctx) (x : Nat) :
    (Γ.dshift).lookup x = (Γ.lookup x).map Tm.dshift := by
  induction Γ generalizing x with
  | nil => rfl
  | cons A Γ ih =>
    cases x with
    | zero => simp [Ctx.dshift, Ctx.lookup, Tm.shift_dshift]
    | succ x =>
      have := ih x
      simp only [Ctx.dshift] at this
      simp [Ctx.dshift, Ctx.lookup, this, Option.map_map, Function.comp_def, Tm.shift_dshift]

theorem Ctx.lookup_cons_succ (A : Tm) (Γ : Ctx) (x : Nat) :
    Ctx.lookup (A :: Γ) (x + 1) = (Ctx.lookup Γ x).map Tm.shift := rfl

/-! ## Derived rules -/

section
variable {S : Sig}

theorem HasTy.liftLe {Ψ Φ Γ A l l'} (h : HasTy S Ψ Φ Γ A (.univ l)) (hl : l ≤ l')
    (hm : l' ≤ maxLevel) : HasTy S Ψ Φ Γ A (.univ l') := by
  induction hl with
  | refl => exact h
  | step hle ih => exact HasTy.cumul hm (ih (Nat.le_of_succ_le hm))

theorem EqTm.liftLe {Ψ Φ Γ A B l l'} (h : EqTm S Ψ Φ Γ A B (.univ l)) (hl : l ≤ l')
    (hm : l' ≤ maxLevel) : EqTm S Ψ Φ Γ A B (.univ l') := by
  induction hl with
  | refl => exact h
  | step hle ih => exact EqTm.cumul hm (ih (Nat.le_of_succ_le hm))

theorem Wf.restrict {Ψ Φ Φ' Γ} (h : Wf S Ψ Φ Γ) (hs : Φ'.Scoped Ψ) (he : I.Entails Φ' Φ) :
    Wf S Ψ Φ' Γ := by
  cases h with
  | nil _ => exact Wf.nil hs
  | cons hA => exact Wf.cons (HasTy.restrict hs he hA)

theorem Wf.dwk {Ψ Φ Γ} (h : Wf S Ψ Φ Γ) (hs : Φ.Scoped Ψ) : Wf S (Ψ + 1) Φ.shift Γ.dshift := by
  cases h with
  | nil _ => exact Wf.nil (I.scoped_shift hs)
  | cons hA => exact Wf.cons (HasTy.dwk hA)

end

end KubusCore
