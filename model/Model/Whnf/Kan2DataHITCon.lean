import Model.Whnf.Kan2DataHITRel
import Model.Whnf.Near

/-!
# Constructors of higher inductive types: syntax and typing

Reduction of constructors at their boundaries, the boundary terms at parameters, arguments and
interval arguments (`Ctor.bndAt`) and their restrictions, and the retyping of constructors to the
parameters of their type.
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

attribute [local instance] Classical.propDecidable

variable {S : Sig} {k k' k'' : ℕ}

/-- `I.Eq`-equal interval arguments, from their pointwise statement. -/
theorem forall2_ieq {rs rs' : List I} (hl : rs.length = rs'.length)
    (h : ∀ (i : ℕ) (r r' : I), rs[i]? = some r → rs'[i]? = some r' → I.Eq r r') : List.Forall₂ I.Eq rs rs' := by
  induction rs generalizing rs' with
  | nil => cases rs' with
    | nil => exact .nil
    | cons _ _ => simp at hl
  | cons r rs ih => cases rs' with
    | nil => simp at hl
    | cons r' rs' =>
      exact .cons (h 0 r r' rfl rfl) (ih (by simpa using hl) fun i x x' hx hx' => h (i + 1) x x' hx hx')

theorem ieq_of_forall2 {rs rs' : List I} (h : List.Forall₂ I.Eq rs rs') :
    rs.length = rs'.length ∧ ∀ (i : ℕ) (r r' : I), rs[i]? = some r → rs'[i]? = some r' → I.Eq r r' := by
  induction h with
  | nil => exact ⟨rfl, fun i r r' h _ => by simp at h⟩
  | cons h1 _ ih =>
    refine ⟨by simp [ih.1], fun i r r' hr hr' => ?_⟩
    cases i with
    | zero => simp at hr hr'; subst hr hr'; exact h1
    | succ i => exact ih.2 i r r' (by simpa using hr) (by simpa using hr')

/-- The interval substitution of the interval arguments. -/
abbrev rsSub (rs : List I) : ℕ → I := fun i => rs.reverse.getD i (.var i)

theorem rsSub_ieq {rs rs' : List I} (h : List.Forall₂ I.Eq rs rs') (i : ℕ) : I.Eq (rsSub rs i) (rsSub rs' i) :=
  ieqL_getD (ieqL_reverse h) _ i

/-- The interval arguments of a nested constructor, at related interval arguments. -/
theorem forall2_map_subst (rs0 : List I) {rs rs' : List I} (h : List.Forall₂ I.Eq rs rs') :
    List.Forall₂ I.Eq (rs0.map (·.subst (rsSub rs))) (rs0.map (·.subst (rsSub rs'))) := by
  induction rs0 with
  | nil => exact .nil
  | cons r rs0 ih => exact .cons (I_eq_subst_congr (rsSub_ieq h) r) ih

theorem forall2_ieq_map {rs rs' : List I} (h : List.Forall₂ I.Eq rs rs') (τ : ℕ → I) :
    List.Forall₂ I.Eq (rs.map (·.subst τ)) (rs'.map (·.subst τ)) := by
  induction h with
  | nil => exact .nil
  | cons h1 _ ih => exact .cons (I_eq_subst h1 τ) ih

theorem forall2_ieq_refl (rs : List I) : List.Forall₂ I.Eq rs rs := by
  induction rs with
  | nil => exact .nil
  | cons r rs ih => exact .cons (I_eq_refl r) ih

theorem forall2_ieq_symm {rs rs' : List I} (h : List.Forall₂ I.Eq rs rs') : List.Forall₂ I.Eq rs' rs := by
  induction h with
  | nil => exact .nil
  | cons h1 _ ih => exact .cons (I_eq_symm h1) ih

/-- The first boundary that holds is not affected by `I.Eq`-equal interval arguments. -/
theorem firstBnd_eq {bnd : List (I × Tm)} {rs rs' : List I} (h : List.Forall₂ I.Eq rs rs') :
    firstBnd bnd rs = firstBnd bnd rs' := firstBnd_near bnd h

theorem firstBnd_none {bnd : List (I × Tm)} {rs : List I} (h : firstBnd bnd rs = none) {kb : ℕ} {ψ : I} {b : Tm}
    (hb : bnd[kb]? = some (ψ, b)) : ¬ I.Entails .one (Ctor.cofAt ψ rs) := by
  intro hent
  unfold firstBnd at h
  split at h
  · cases h
  · rename_i hn
    have hm : (ψ, b) ∈ bnd := List.mem_of_getElem? hb
    have := List.find?_eq_none.1 hn (ψ, b) hm
    exact this (by simpa using hent)

/-- Boundaries that hold keep holding at restrictions. -/
theorem firstBnd_isSome_subst {bnd : List (I × Tm)} {rs : List I} {b : Tm} (h : firstBnd bnd rs = some b)
    (hsc : ∀ p ∈ bnd, p.1.Scoped rs.length) (τ : ℕ → I) :
    ∃ b', firstBnd bnd (rs.map (·.subst τ)) = some b' := by
  obtain ⟨kb, ψ, hb, hent⟩ := firstBnd_spec h
  cases hf : firstBnd bnd (rs.map (·.subst τ)) with
  | some b' => exact ⟨b', rfl⟩
  | none =>
    exfalso
    have hψ := hsc (ψ, b) (List.mem_of_getElem? hb)
    refine firstBnd_none hf hb ?_
    rw [← cofAt_subst τ hψ]
    exact ent_one_subst hent τ

section red
variable {d : ℕ} {D : DataDecl} (hD : S[d]? = some (.data D))
include hD

/-- A constructor where no boundary holds is a weak-head normal form. -/
theorem step_con_none {c : ℕ} {C : Ctor} (hC : D.ctors[c]? = some C) (ps args : Tm) {rs : List I}
    (h : firstBnd C.bnd rs = none) : step S (.con d c ps args rs) = none := by
  simp [step, hD, hC, h]

/-- A constructor where a boundary holds reduces to the first such boundary. -/
theorem step_con_some {c : ℕ} {C : Ctor} (hC : D.ctors[c]? = some C) (ps args : Tm) {rs : List I} {b : Tm}
    (h : firstBnd C.bnd rs = some b) :
    step S (.con d c ps args rs) = some (Ctor.bndAt b ps.toList args.toList rs) := by
  simp [step, hD, hC, h]

end red

/-! ### Boundary terms -/

theorem bndAt_var {x : ℕ} {ps args : List Tm} (rs : List I) (hx : x < args.length) :
    Ctor.bndAt (.var x) ps args rs = args.getD (args.length - 1 - x) .abort := by
  simp only [Ctor.bndAt, Tm.subst, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left (by simp; omega), List.getElem?_reverse hx,
    List.getElem?_eq_getElem (by omega)]
  simp

theorem bndAt_con (d' c' : ℕ) (ps0 as0 : Tm) (rs0 : List I) (ps args : List Tm) (rs : List I) :
    Ctor.bndAt (.con d' c' ps0 as0 rs0) ps args rs =
      .con d' c' (Ctor.bndAt ps0 ps args rs) (Ctor.bndAt as0 ps args rs) (rs0.map (·.subst (rsSub rs))) := by
  simp only [Ctor.bndAt, Tm.subst]

theorem bndAt_tcons (a as0 : Tm) (ps args : List Tm) (rs : List I) :
    Ctor.bndAt (.tcons a as0) ps args rs = .tcons (Ctor.bndAt a ps args rs) (Ctor.bndAt as0 ps args rs) := by
  simp only [Ctor.bndAt, Tm.subst]

theorem bndAt_ofList (L : List Tm) (ps args : List Tm) (rs : List I) :
    Ctor.bndAt (Tm.ofList L) ps args rs = Tm.ofList (L.map fun a => Ctor.bndAt a ps args rs) := by
  induction L with
  | nil => simp [Tm.ofList, Ctor.bndAt, Tm.subst]
  | cons a L ih => simp only [Tm.ofList, List.map_cons]; rw [bndAt_tcons, ih]

theorem bndAt_paramVars {ps args : List Tm} (rs : List I) {np n : ℕ} (hp : ps.length = np) (hn : args.length = n) :
    Ctor.bndAt (Ctor.paramVars np n) ps args rs = Tm.ofList ps := by
  subst hp hn
  rw [Ctor.paramVars, bndAt_ofList, List.map_map]
  congr 1
  apply List.ext_getElem (by simp)
  intro p h1 h2
  simp only [List.length_map, List.length_range] at h1
  simp only [List.getElem_map, List.getElem_range, Function.comp_apply, Ctor.bndAt, Tm.subst,
    List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by simp; omega), List.getElem?_reverse (by simp; omega)]
  simp only [List.length_reverse]
  rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
  congr 1; omega

/-- A boundary term, restricted. -/
theorem bndAt_isub {b : Tm} {ps args : List Tm} {rs : List I}
    (hb : b.closedB (ps.length + args.length) rs.length = true) (σ : ISub k' k) :
    (Ctor.bndAt b ps args rs).isub σ =
      Ctor.bndAt b (ps.map (·.isub σ)) (args.map (·.isub σ)) (rs.map (·.subst σ.τ)) :=
  bndAt_subst _ _ hb

end

end Model.Whnf
