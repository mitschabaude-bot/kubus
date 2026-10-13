import KubusCore.Rules

/-!
# Metatheory: the substitution calculus

σ-calculus style lemmas for `I.subst` and `Tm.subst`/`Tm.ren`: renaming and substitution
fuse, renamings are substitutions, and the identity substitution is the identity. Every
other syntactic commutation in `KubusCore/Meta` is reduced to these by pointwise
calculations on substitutions.
-/

namespace KubusCore.Meta

open Tm

/-! ## Interval terms -/

theorem I_subst_subst (σ τ : Nat → I) (r : I) :
    (r.subst σ).subst τ = r.subst fun i => (σ i).subst τ := by
  induction r <;> simp_all [I.subst]

theorem I_subst_var (r : I) : r.subst I.var = r := by
  induction r <;> simp_all [I.subst]

theorem I_subst_congr {σ τ : Nat → I} (h : ∀ i, σ i = τ i) (r : I) : r.subst σ = r.subst τ := by
  rw [funext h]

theorem I_ren_eq (δ : Nat → Nat) (r : I) : r.ren δ = r.subst (fun i => .var (δ i)) := rfl

theorem I_ren_subst (δ : Nat → Nat) (τ : Nat → I) (r : I) :
    (r.ren δ).subst τ = r.subst (fun i => τ (δ i)) := by
  simp only [I.ren, I_subst_subst]; rfl

theorem I_subst_ren (δ : Nat → Nat) (τ : Nat → I) (r : I) :
    (r.subst τ).ren δ = r.subst (fun i => (τ i).ren δ) := by
  simp only [I.ren, I_subst_subst]

theorem I_ren_ren (δ δ' : Nat → Nat) (r : I) : (r.ren δ).ren δ' = r.ren (fun i => δ' (δ i)) := by
  simp only [I.ren, I_subst_subst]; rfl

theorem I_ren_id (r : I) : r.ren id = r := I_subst_var r

theorem I_up_comp (σ τ : Nat → I) (i : Nat) :
    (I.up σ i).subst (I.up τ) = I.up (fun i => (σ i).subst τ) i := by
  cases i with
  | zero => rfl
  | succ n =>
    simp only [I.up, I.shift, I_ren_subst, I_subst_ren]

theorem I_up_var : I.up I.var = I.var := by funext n; cases n <;> rfl

theorem I_shift_subst_up (τ : Nat → I) (r : I) : r.shift.subst (I.up τ) = (r.subst τ).shift := by
  simp only [I.shift, I_ren_subst, I_subst_ren]; rfl

theorem I_up_ren (δ : Nat → Nat) : I.up (fun i => .var (δ i)) = fun i => .var (upRen δ i) := by
  funext n; cases n <;> rfl

/-! ## Terms -/

theorem upRen_comp (ρ ρ' : Nat → Nat) : (fun n => upRen ρ' (upRen ρ n)) = upRen (fun n => ρ' (ρ n)) := by
  funext n; cases n <;> rfl

theorem ren_ren (t : Tm) : ∀ (ρ δ ρ' δ' : Nat → Nat),
    (t.ren ρ δ).ren ρ' δ' = t.ren (fun n => ρ' (ρ n)) (fun n => δ' (δ n)) := by
  induction t <;> intros <;>
    simp_all [ren, I_ren_ren, upRen_comp, List.map_map, Function.comp_def]

theorem up_upRen (σ : Nat → Tm) (ρ : Nat → Nat) : (fun n => up σ (upRen ρ n)) = up (fun n => σ (ρ n)) := by
  funext n; cases n <;> rfl

theorem Iup_upRen (τ : Nat → I) (δ : Nat → Nat) :
    (fun n => I.up τ (upRen δ n)) = I.up (fun n => τ (δ n)) := by
  funext n; cases n <;> rfl

/-- Substitution after renaming. -/
theorem subst_ren (t : Tm) : ∀ (ρ δ : Nat → Nat) (σ : Nat → Tm) (τ : Nat → I),
    (t.ren ρ δ).subst σ τ = t.subst (fun n => σ (ρ n)) (fun i => τ (δ i)) := by
  induction t <;> intros <;>
    simp_all [ren, subst, I_ren_subst, up_upRen, Iup_upRen, List.map_map, Function.comp_def]

theorem upRen_succ (ρ : Nat → Nat) : (fun n => upRen ρ (Nat.succ n)) = fun n => Nat.succ (ρ n) := rfl

/-- Renaming after substitution. -/
theorem ren_subst (t : Tm) : ∀ (ρ δ : Nat → Nat) (σ : Nat → Tm) (τ : Nat → I),
    (t.subst σ τ).ren ρ δ = t.subst (fun n => (σ n).ren ρ δ) (fun i => (τ i).ren δ) := by
  induction t with
  | var x => intros; rfl
  | pi A B ihA ihB | sigma A B ihA ihB | lam A B ihA ihB =>
    intro ρ δ σ τ
    simp only [subst, ren, ihA, ihB]
    congr 2
    funext n; cases n with
    | zero => rfl
    | succ n => simp only [up, shift, ren_ren]; rfl
  | elim d ps P bs t ihps ihP ihbs iht =>
    intro ρ δ σ τ
    simp only [subst, ren, ihps, ihP, ihbs, iht]
    congr 2
    funext n; cases n with
    | zero => rfl
    | succ n => simp only [up, shift, ren_ren]; rfl
  | path A a b ihA iha ihb =>
    intro ρ δ σ τ
    simp only [subst, ren, ihA, iha, ihb]
    congr 2
    · funext n; simp only [dshift, ren_ren]; rfl
    · funext n; cases n with
      | zero => rfl
      | succ n => simp only [I.up, I.shift, I_ren_ren]; rfl
  | plam t ih | ipi t ih =>
    intro ρ δ σ τ
    simp only [subst, ren, ih]
    congr 2
    · funext n; simp only [dshift, ren_ren]; rfl
    · funext n; cases n with
      | zero => rfl
      | succ n => simp only [I.up, I.shift, I_ren_ren]; rfl
  | transp A φ a ihA iha =>
    intro ρ δ σ τ
    simp only [subst, ren, ihA, iha, I_subst_ren]
    congr 2
    · funext n; simp only [dshift, ren_ren]; rfl
    · funext n; cases n with
      | zero => rfl
      | succ n => simp only [I.up, I.shift, I_ren_ren]; rfl
  | hcomp A φ u a ihA ihu iha =>
    intro ρ δ σ τ
    simp only [subst, ren, ihA, ihu, iha, I_subst_ren]
    congr 2
    · funext n; simp only [dshift, ren_ren]; rfl
    · funext n; cases n with
      | zero => rfl
      | succ n => simp only [I.up, I.shift, I_ren_ren]; rfl
  | _ => intros; simp_all [subst, ren, I_subst_ren, List.map_map, Function.comp_def]

theorem up_comp (σ σ' : Nat → Tm) (τ' : Nat → I) (n : Nat) :
    (up σ n).subst (up σ') τ' = up (fun n => (σ n).subst σ' τ') n := by
  cases n with
  | zero => rfl
  | succ n =>
    simp only [up, shift, subst_ren, ren_subst]
    congr 1
    funext i; simp [I.ren, I_subst_var]

theorem dshift_comp (σ σ' : Nat → Tm) (τ' : Nat → I) (n : Nat) :
    ((σ n).dshift).subst (fun n => (σ' n).dshift) (I.up τ') = ((σ n).subst σ' τ').dshift := by
  simp only [dshift, subst_ren, ren_subst]
  rfl

/-- Substitutions compose. -/
theorem subst_subst (t : Tm) : ∀ (σ : Nat → Tm) (τ : Nat → I) (σ' : Nat → Tm) (τ' : Nat → I),
    (t.subst σ τ).subst σ' τ' = t.subst (fun n => (σ n).subst σ' τ') (fun i => (τ i).subst τ') := by
  induction t with
  | var x => intros; rfl
  | pi A B ihA ihB | sigma A B ihA ihB | lam A B ihA ihB =>
    intro σ τ σ' τ'
    simp only [subst, ihA, ihB]
    congr 2; funext n; exact up_comp σ σ' τ' n
  | elim d ps P bs t ihps ihP ihbs iht =>
    intro σ τ σ' τ'
    simp only [subst, ihps, ihP, ihbs, iht]
    congr 2; funext n; exact up_comp σ σ' τ' n
  | path A a b ihA iha ihb =>
    intro σ τ σ' τ'
    simp only [subst, ihA, iha, ihb]
    congr 2
    · funext n; exact dshift_comp σ σ' τ' n
    · funext n; exact I_up_comp τ τ' n
  | plam t ih | ipi t ih =>
    intro σ τ σ' τ'
    simp only [subst, ih]
    congr 2
    · funext n; exact dshift_comp σ σ' τ' n
    · funext n; exact I_up_comp τ τ' n
  | transp A φ a ihA iha =>
    intro σ τ σ' τ'
    simp only [subst, ihA, iha, I_subst_subst]
    congr 2
    · funext n; exact dshift_comp σ σ' τ' n
    · funext n; exact I_up_comp τ τ' n
  | hcomp A φ u a ihA ihu iha =>
    intro σ τ σ' τ'
    simp only [subst, ihA, ihu, iha, I_subst_subst]
    congr 2
    · funext n; exact dshift_comp σ σ' τ' n
    · funext n; exact I_up_comp τ τ' n
  | _ => intros; simp_all [subst, I_subst_subst, List.map_map, Function.comp_def]

theorem up_var : up Tm.var = Tm.var := by funext n; cases n <;> rfl

theorem subst_var (t : Tm) : t.subst Tm.var I.var = t := by
  induction t <;>
    simp_all [subst, up_var, I_up_var, I_subst_var, dshift, ren] <;>
    first | rfl | (apply List.map_id'; intro r; exact I_subst_var r) | skip

theorem subst_congr {σ σ' : Nat → Tm} {τ τ' : Nat → I} (h1 : ∀ n, σ n = σ' n) (h2 : ∀ i, τ i = τ' i)
    (t : Tm) : t.subst σ τ = t.subst σ' τ' := by
  rw [funext h1, funext h2]

/-- Renamings are substitutions. -/
theorem ren_eq_subst (t : Tm) : ∀ (ρ δ : Nat → Nat),
    t.ren ρ δ = t.subst (fun n => .var (ρ n)) (fun i => .var (δ i)) := by
  intro ρ δ
  have h := subst_ren t ρ δ Tm.var I.var
  rw [subst_var] at h
  exact h

theorem subst_id_of {σ : Nat → Tm} {τ : Nat → I} (h1 : ∀ n, σ n = .var n) (h2 : ∀ i, τ i = .var i)
    (t : Tm) : t.subst σ τ = t := by
  rw [subst_congr h1 h2, subst_var]

/-! ### Common instances -/

theorem shift_eq (t : Tm) : t.shift = t.subst (fun n => .var (n + 1)) I.var := by
  rw [shift, ren_eq_subst]; rfl

theorem dshift_eq (t : Tm) : t.dshift = t.subst Tm.var (fun i => .var (i + 1)) := by
  rw [dshift, ren_eq_subst]; rfl

theorem shift_subst (t : Tm) (σ : Nat → Tm) (τ : Nat → I) :
    t.shift.subst σ τ = t.subst (fun n => σ (n + 1)) τ := by
  rw [shift, subst_ren]; rfl

theorem dshift_subst (t : Tm) (σ : Nat → Tm) (τ : Nat → I) :
    t.dshift.subst σ τ = t.subst σ (fun i => τ (i + 1)) := by
  rw [dshift, subst_ren]; rfl

theorem subst_shift (t : Tm) (σ : Nat → Tm) (τ : Nat → I) :
    (t.subst σ τ).shift = t.subst (fun n => (σ n).shift) τ := by
  rw [shift, ren_subst]; simp only [I_ren_id]; rfl

theorem subst_dshift (t : Tm) (σ : Nat → Tm) (τ : Nat → I) :
    (t.subst σ τ).dshift = t.subst (fun n => (σ n).dshift) (fun i => (τ i).shift) := by
  rw [dshift, ren_subst]; rfl

theorem shift_inst (t a : Tm) : t.shift.inst a = t := by
  rw [inst, shift_subst]; exact subst_id_of (fun _ => rfl) (fun _ => rfl) t

theorem dshift_dinst (t : Tm) (r : I) : t.dshift.dinst r = t := by
  rw [dinst, dsubst, dshift_subst]; exact subst_id_of (fun _ => rfl) (fun _ => rfl) t

theorem shift_dshift (t : Tm) : t.shift.dshift = t.dshift.shift := by
  simp only [shift, dshift, ren_ren]; rfl

/-- `(t[a/0])σ = (t σ⁺)[a σ/0]` -/
theorem inst_subst (t a : Tm) (σ : Nat → Tm) (τ : Nat → I) :
    (t.inst a).subst σ τ = (t.subst (up σ) τ).inst (a.subst σ τ) := by
  simp only [inst, subst_subst]
  apply subst_congr
  · intro n; cases n with
    | zero => rfl
    | succ n => simp only [up, shift_subst]; exact (subst_id_of (fun _ => rfl) (fun _ => rfl) _).symm
  · intro i; simp [I.subst, I_subst_var]

/-- `(t[r/0])τ = (t τ⁺)[r τ/0]` -/
theorem dinst_subst (t : Tm) (r : I) (σ : Nat → Tm) (τ : Nat → I) :
    (t.dinst r).subst σ τ = (t.subst (fun n => (σ n).dshift) (I.up τ)).dinst (r.subst τ) := by
  simp only [dinst, dsubst, subst_subst]
  apply subst_congr
  · intro n; simp only [subst]; rw [dshift_subst]
    exact (subst_id_of (fun _ => rfl) (fun i => rfl) _).symm
  · intro i; cases i with
    | zero => rfl
    | succ n =>
      simp only [I.inst0, I.subst, I.up, I.shift, I_ren_subst]
      exact (I_subst_var _).symm

theorem inst_ren (t a : Tm) (ρ δ : Nat → Nat) :
    (t.inst a).ren ρ δ = (t.ren (upRen ρ) δ).inst (a.ren ρ δ) := by
  simp only [ren_eq_subst, inst_subst]
  congr 2
  · funext n; cases n <;> rfl

theorem dinst_ren (t : Tm) (r : I) (ρ δ : Nat → Nat) :
    (t.dinst r).ren ρ δ = (t.ren ρ (upRen δ)).dinst (r.ren δ) := by
  simp only [ren_eq_subst, dinst_subst]
  congr 2
  funext n; cases n <;> rfl

theorem tyHead_subst {X : Tm} {h : Nat × Nat} (σ : Nat → Tm) (τ : Nat → I) (hX : X.tyHead = some h) :
    (X.subst σ τ).tyHead = some h := by
  cases X <;> first | exact hX | (simp [Tm.tyHead] at hX)

theorem headClash_subst {X Y : Tm} (σ : Nat → Tm) (τ : Nat → I) (h : X.headClash Y = true) :
    (X.subst σ τ).headClash (Y.subst σ τ) = true := by
  unfold Tm.headClash at h ⊢
  cases hX : X.tyHead with
  | none => rw [hX] at h; simp at h
  | some a =>
    cases hY : Y.tyHead with
    | none => rw [hX, hY] at h; simp at h
    | some b => rw [hX, hY] at h; rw [tyHead_subst σ τ hX, tyHead_subst σ τ hY]; exact h

end KubusCore.Meta
