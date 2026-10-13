import KubusCore.Syntax
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod

/-!
# The interval and the face lattice

* `M4` laws (the spec defines `M4` and `I.eval`).
* Soundness of the spec's disjunctive normal form `I.dnf` for `M4`-evaluation.
* The face lattice is the Kleene algebra `K3 = {0, a, 1} ⊆ M4`: a cofibration `r` holds at a
  partial 0/1-assignment iff `r` evaluates to `1` there, reading "undefined" as `a`.
  We prove that the spec's `I.Entails` is sound for this reading (`entails_sound`).
* `r = 1` in the free De Morgan algebra iff `r` evaluates to `1` when all variables are `a`
  (`eval_allA_eq_one`): this is the criterion "a face holds at a stage".
-/

set_option autoImplicit false

namespace Model

open KubusCore

abbrev M4 := I.M4

namespace M4

open I.M4

instance : Fintype M4 where
  elems := {zero, a, b, one}
  complete x := by cases x <;> simp

instance : Min M4 := ⟨meet⟩
instance : Max M4 := ⟨join⟩

@[simp] theorem meet_zero_left (x : M4) : meet zero x = zero := by cases x <;> rfl
@[simp] theorem meet_zero_right (x : M4) : meet x zero = zero := by cases x <;> rfl
@[simp] theorem meet_one_left (x : M4) : meet one x = x := by cases x <;> rfl
@[simp] theorem meet_one_right (x : M4) : meet x one = x := by cases x <;> rfl
@[simp] theorem join_zero_left (x : M4) : join zero x = x := by cases x <;> rfl
@[simp] theorem join_zero_right (x : M4) : join x zero = x := by cases x <;> rfl
@[simp] theorem join_one_left (x : M4) : join one x = one := by cases x <;> rfl
@[simp] theorem join_one_right (x : M4) : join x one = one := by cases x <;> rfl
@[simp] theorem neg_neg (x : M4) : neg (neg x) = x := by cases x <;> rfl
@[simp] theorem neg_zero : neg zero = one := rfl
@[simp] theorem neg_one : neg one = zero := rfl
@[simp] theorem neg_a : neg a = a := rfl
@[simp] theorem neg_b : neg b = b := rfl
@[simp] theorem meet_self (x : M4) : meet x x = x := by cases x <;> rfl
@[simp] theorem join_self (x : M4) : join x x = x := by cases x <;> rfl
theorem meet_comm (x y : M4) : meet x y = meet y x := by cases x <;> cases y <;> rfl
theorem join_comm (x y : M4) : join x y = join y x := by cases x <;> cases y <;> rfl
theorem meet_assoc (x y z : M4) : meet (meet x y) z = meet x (meet y z) := by
  cases x <;> cases y <;> cases z <;> rfl
theorem join_assoc (x y z : M4) : join (join x y) z = join x (join y z) := by
  cases x <;> cases y <;> cases z <;> rfl
theorem neg_meet (x y : M4) : neg (meet x y) = join (neg x) (neg y) := by
  cases x <;> cases y <;> rfl
theorem neg_join (x y : M4) : neg (join x y) = meet (neg x) (neg y) := by
  cases x <;> cases y <;> rfl
theorem meet_join_distrib (x y z : M4) : meet x (join y z) = join (meet x y) (meet x z) := by
  cases x <;> cases y <;> cases z <;> rfl
theorem join_meet_distrib (x y z : M4) : join x (meet y z) = meet (join x y) (join x z) := by
  cases x <;> cases y <;> cases z <;> rfl
theorem meet_join_distrib_right (x y z : M4) :
    meet (join x y) z = join (meet x z) (meet y z) := by
  cases x <;> cases y <;> cases z <;> rfl
theorem join_meet_distrib_right (x y z : M4) :
    join (meet x y) z = meet (join x z) (join y z) := by
  cases x <;> cases y <;> cases z <;> rfl

theorem meet_eq_one {x y : M4} : meet x y = one ↔ x = one ∧ y = one := by
  cases x <;> cases y <;> decide

/-- The Kleene subalgebra `{0, a, 1}`. -/
def IsK3 (x : M4) : Prop := x ≠ b

instance : DecidablePred IsK3 := fun x => inferInstanceAs (Decidable (x ≠ b))

theorem IsK3.meet {x y : M4} (hx : IsK3 x) (hy : IsK3 y) : IsK3 (I.M4.meet x y) := by
  revert hx hy; cases x <;> cases y <;> decide
theorem IsK3.join {x y : M4} (hx : IsK3 x) (hy : IsK3 y) : IsK3 (I.M4.join x y) := by
  revert hx hy; cases x <;> cases y <;> decide
theorem IsK3.neg {x : M4} (hx : IsK3 x) : IsK3 (I.M4.neg x) := by
  revert hx; cases x <;> decide

/-- In `K3` (a chain), a join is `1` iff one of the arguments is. -/
theorem join_eq_one_K3 {x y : M4} (hx : IsK3 x) (hy : IsK3 y) :
    join x y = one ↔ x = one ∨ y = one := by
  revert hx hy; cases x <;> cases y <;> decide

end M4

namespace Cof

open KubusCore.I.M4 Model.M4
open KubusCore.I (dnf Face Entails entails eval faces)

theorem eval_subst (σ : ℕ → I) (ρ : ℕ → M4) (r : I) :
    (r.subst σ).eval ρ = r.eval (fun n => (σ n).eval ρ) := by
  induction r <;> simp_all [I.subst, I.eval]

theorem eval_congr {ρ ρ' : ℕ → M4} {r : I} {m : ℕ} (hr : r.Scoped m)
    (h : ∀ n, n < m → ρ n = ρ' n) : r.eval ρ = r.eval ρ' := by
  induction r <;> simp_all [I.eval, I.Scoped]

theorem scoped_subst {σ : ℕ → I} {r : I} {m k : ℕ} (hr : r.Scoped m)
    (hσ : ∀ n, n < m → (σ n).Scoped k) : (r.subst σ).Scoped k := by
  induction r <;> simp_all [I.subst, I.Scoped]

theorem scoped_mono {r : I} {m k : ℕ} (hr : r.Scoped m) (h : m ≤ k) : r.Scoped k := by
  induction r <;> simp_all [I.Scoped]; omega

/-! ### Disjunctive normal forms -/

def litVal (ρ : ℕ → M4) : ℕ × Bool → M4
  | (i, true) => ρ i
  | (i, false) => neg (ρ i)

def clauseVal (ρ : ℕ → M4) (c : Face) : M4 := c.foldr (fun l acc => meet (litVal ρ l) acc) one

def dnfVal (ρ : ℕ → M4) (cs : List Face) : M4 := cs.foldr (fun c acc => join (clauseVal ρ c) acc) zero

theorem clauseVal_append (ρ : ℕ → M4) (c d : Face) :
    clauseVal ρ (c ++ d) = meet (clauseVal ρ c) (clauseVal ρ d) := by
  induction c with
  | nil => simp [clauseVal]
  | cons l c ih => simp only [clauseVal, List.cons_append, List.foldr_cons] at *; rw [ih, meet_assoc]

theorem dnfVal_append (ρ : ℕ → M4) (cs ds : List Face) :
    dnfVal ρ (cs ++ ds) = join (dnfVal ρ cs) (dnfVal ρ ds) := by
  induction cs with
  | nil => simp [dnfVal]
  | cons c cs ih => simp only [dnfVal, List.cons_append, List.foldr_cons] at *; rw [ih, join_assoc]

theorem dnfVal_map_append (ρ : ℕ → M4) (c : Face) (ds : List Face) :
    dnfVal ρ (ds.map (c ++ ·)) = meet (clauseVal ρ c) (dnfVal ρ ds) := by
  induction ds with
  | nil => simp [dnfVal]
  | cons d ds ih =>
    simp only [dnfVal, List.map_cons, List.foldr_cons] at *
    rw [ih, clauseVal_append, meet_join_distrib]

theorem dnfVal_flatMap (ρ : ℕ → M4) (cs ds : List Face) :
    dnfVal ρ (cs.flatMap fun c => ds.map (c ++ ·)) = meet (dnfVal ρ cs) (dnfVal ρ ds) := by
  induction cs with
  | nil => simp [dnfVal]
  | cons c cs ih =>
    simp only [List.flatMap_cons, dnfVal_append, dnfVal_map_append, ih]
    simp only [dnfVal, List.foldr_cons]
    rw [meet_join_distrib_right]

/-- The spec's DNF is sound for `M4`-evaluation. -/
theorem dnfVal_dnf (ρ : ℕ → M4) (r : I) :
    dnfVal ρ (dnf true r) = r.eval ρ ∧ dnfVal ρ (dnf false r) = neg (r.eval ρ) := by
  induction r with
  | zero => simp [dnf, dnfVal, clauseVal, eval]
  | one => simp [dnf, dnfVal, clauseVal, eval]
  | var i => simp [dnf, dnfVal, clauseVal, eval, litVal]
  | neg r ih => simp [dnf, eval, ih.1, ih.2]
  | and r s ihr ihs =>
    refine ⟨?_, ?_⟩
    · simp only [dnf, dnfVal_flatMap, ihr.1, ihs.1, eval]
    · simp only [dnf, dnfVal_append, ihr.2, ihs.2, eval, neg_meet]
  | or r s ihr ihs =>
    refine ⟨?_, ?_⟩
    · simp only [dnf, dnfVal_append, ihr.1, ihs.1, eval]
    · simp only [dnf, dnfVal_flatMap, ihr.2, ihs.2, eval, neg_join]

/-! ### The Kleene reading -/

/-- A literal holds at `ρ` (as a 0/1 constraint). -/
def LitHolds (ρ : ℕ → M4) (l : ℕ × Bool) : Prop := ρ l.1 = if l.2 then one else zero

theorem litVal_eq_one (ρ : ℕ → M4) (l : ℕ × Bool) : litVal ρ l = one ↔ LitHolds ρ l := by
  obtain ⟨i, d⟩ := l
  simp only [litVal, LitHolds]
  cases d <;> cases h : ρ i <;> simp [h]

theorem clauseVal_eq_one (ρ : ℕ → M4) (c : Face) :
    clauseVal ρ c = one ↔ ∀ l ∈ c, LitHolds ρ l := by
  induction c with
  | nil => simp [clauseVal]
  | cons l c ih =>
    simp only [clauseVal, List.foldr_cons] at *
    rw [meet_eq_one, ih, litVal_eq_one]; simp

theorem litVal_K3 {ρ : ℕ → M4} (hρ : ∀ n, IsK3 (ρ n)) (l : ℕ × Bool) : IsK3 (litVal ρ l) := by
  obtain ⟨i, d⟩ := l; cases d
  · exact (hρ i).neg
  · exact hρ i

theorem clauseVal_K3 {ρ : ℕ → M4} (hρ : ∀ n, IsK3 (ρ n)) (c : Face) : IsK3 (clauseVal ρ c) := by
  induction c with
  | nil => simp [clauseVal, IsK3]
  | cons l c ih => exact (litVal_K3 hρ l).meet ih

theorem dnfVal_eq_one_K3 {ρ : ℕ → M4} (hρ : ∀ n, IsK3 (ρ n)) (cs : List Face) :
    dnfVal ρ cs = one ↔ ∃ c ∈ cs, ∀ l ∈ c, LitHolds ρ l := by
  induction cs with
  | nil => simp [dnfVal]
  | cons c cs ih =>
    have hK : IsK3 (dnfVal ρ cs) := by
      clear ih; induction cs with
      | nil => simp [dnfVal, IsK3]
      | cons d ds ih' => exact (clauseVal_K3 hρ d).join ih'
    simp only [dnfVal, List.foldr_cons] at *
    rw [join_eq_one_K3 (clauseVal_K3 hρ c) hK, ih, clauseVal_eq_one]; simp

theorem consistent_of_holds {ρ : ℕ → M4} {c : Face} (h : ∀ l ∈ c, LitHolds ρ l) :
    c.consistent = true := by
  simp only [Face.consistent, List.all_eq_true]
  intro ⟨i, d⟩ hl
  simp only [Bool.not_eq_eq_eq_not, Bool.not_true, List.contains_iff_mem]
  simp only [List.elem_eq_mem, decide_eq_false_iff_not]
  intro hl'
  have h1 := h _ hl; have h2 := h _ hl'
  simp only [LitHolds] at h1 h2
  rw [h1] at h2; cases d <;> simp at h2

/-- At a `K3`-point, `r = 1` iff some face of `r` holds. -/
theorem eval_eq_one_iff_faces {ρ : ℕ → M4} (hρ : ∀ n, IsK3 (ρ n)) (r : I) :
    r.eval ρ = one ↔ ∃ c ∈ r.faces, ∀ l ∈ c, LitHolds ρ l := by
  rw [← (dnfVal_dnf ρ r).1, dnfVal_eq_one_K3 hρ]
  constructor
  · rintro ⟨c, hc, h⟩
    exact ⟨c, List.mem_filter.2 ⟨hc, consistent_of_holds h⟩, h⟩
  · rintro ⟨c, hc, h⟩
    exact ⟨c, (List.mem_filter.1 hc).1, h⟩

/-- The spec's entailment is sound for the Kleene reading of cofibrations. -/
theorem entails_sound {φ ψ : I} (h : Entails φ ψ) {ρ : ℕ → M4} (hρ : ∀ n, IsK3 (ρ n))
    (hφ : φ.eval ρ = one) : ψ.eval ρ = one := by
  rw [eval_eq_one_iff_faces hρ] at hφ ⊢
  obtain ⟨c, hc, hcρ⟩ := hφ
  simp only [Entails, entails, List.all_eq_true, List.any_eq_true] at h
  obtain ⟨d, hd, hdc⟩ := h c hc
  refine ⟨d, hd, fun l hl => hcρ l ?_⟩
  simp only [List.all_eq_true, List.contains_iff_mem] at hdc
  simpa using hdc l hl

/-- Equal interval terms have the same Kleene reading (trivially, `K3 ⊆ M4`). -/
theorem Eq.eval {r s : I} (h : I.Eq r s) (ρ : ℕ → M4) : r.eval ρ = s.eval ρ := h ρ

/-! ### `r = 1` iff `r(a, …, a) = 1` -/

theorem clauseVal_allA_ne_one {c : Face} (hc : c ≠ []) : clauseVal (fun _ => a) c ≠ one := by
  rw [Ne, clauseVal_eq_one]
  obtain ⟨⟨i, d⟩, c', rfl⟩ := List.exists_cons_of_ne_nil hc
  intro h
  have := h _ List.mem_cons_self
  cases d <;> simp [LitHolds] at this

theorem eval_allA_eq_one {r : I} (h : r.eval (fun _ => a) = one) (ρ : ℕ → M4) :
    r.eval ρ = one := by
  have hK : ∀ n, IsK3 ((fun _ => a : ℕ → M4) n) := fun _ => by simp [IsK3]
  rw [← (dnfVal_dnf _ r).1, dnfVal_eq_one_K3 hK] at h
  obtain ⟨c, hc, hcl⟩ := h
  have hc0 : c = [] := by
    by_contra hne
    exact clauseVal_allA_ne_one hne ((clauseVal_eq_one _ _).2 hcl)
  subst hc0
  rw [← (dnfVal_dnf ρ r).1]
  generalize dnf true r = cs at hc
  induction cs with
  | nil => simp at hc
  | cons d ds ih =>
    simp only [dnfVal, List.foldr_cons]
    rcases List.mem_cons.1 hc with rfl | h
    · simp [clauseVal]
    · rw [show List.foldr (fun c acc => join (clauseVal ρ c) acc) zero ds = dnfVal ρ ds from rfl,
        ih h, join_one_right]

end Cof

end Model
