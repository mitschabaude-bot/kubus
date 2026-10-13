import Model.CubeLemmas

/-!
# `∀ i. φ` for faces

`Cof.forall0 φ` (for a face `φ` at stage `n + 1`, `i` the last variable) is the face at stage
`n` of the points `p` with `(p, a) ∈ φ`: since a face at `i = a` cannot mention `i`, this is the
spec's `I.forall0` (the clauses of `φ` that do not mention `i`), and it entails `φ` at every
value of `i`.
-/

set_option autoImplicit false

namespace Model

open KubusCore KubusCore.I.M4 Model.M4 Model.Cof
open KubusCore.I (dnf Face faces)

variable {k m n : ℕ}

theorem eval_ofFace (v : ℕ → M4) (α : Face) : (I.ofFace α).eval v = clauseVal v α := by
  induction α with
  | nil => rfl
  | cons l α ih =>
    obtain ⟨i, d⟩ := l
    show I.M4.meet ((I.lit i d).eval v) ((I.ofFace α).eval v) = meet (litVal v (i, d)) (clauseVal v α)
    rw [ih]
    cases d <;> rfl

theorem eval_ofFaces (v : ℕ → M4) (cs : List Face) : (I.ofFaces cs).eval v = dnfVal v cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    show I.M4.join ((I.ofFace c).eval v) ((I.ofFaces cs).eval v) = join (clauseVal v c) (dnfVal v cs)
    rw [ih, eval_ofFace]

theorem dnf_scoped {r : I} {m : ℕ} (hr : r.Scoped m) : ∀ pos, ∀ c ∈ dnf pos r, ∀ l ∈ c, l.1 < m := by
  induction r with
  | zero => intro pos; cases pos <;> simp [dnf]
  | one => intro pos; cases pos <;> simp [dnf]
  | var i => intro pos c hc l hl; simp [dnf] at hc; subst hc; simp at hl; subst hl; exact hr
  | neg r ih => intro pos; cases pos <;> simpa [dnf] using ih hr _
  | and r s ihr ihs =>
    intro pos; cases pos
    · intro c hc l hl
      simp only [dnf, List.mem_append] at hc
      rcases hc with hc | hc
      · exact ihr hr.1 false c hc l hl
      · exact ihs hr.2 false c hc l hl
    · intro c hc l hl
      simp only [dnf, List.mem_flatMap, List.mem_map] at hc
      obtain ⟨c1, hc1, c2, hc2, rfl⟩ := hc
      rcases List.mem_append.1 hl with hl | hl
      · exact ihr hr.1 true c1 hc1 l hl
      · exact ihs hr.2 true c2 hc2 l hl
  | or r s ihr ihs =>
    intro pos; cases pos
    · intro c hc l hl
      simp only [dnf, List.mem_flatMap, List.mem_map] at hc
      obtain ⟨c1, hc1, c2, hc2, rfl⟩ := hc
      rcases List.mem_append.1 hl with hl | hl
      · exact ihr hr.1 false c1 hc1 l hl
      · exact ihs hr.2 false c2 hc2 l hl
    · intro c hc l hl
      simp only [dnf, List.mem_append] at hc
      rcases hc with hc | hc
      · exact ihr hr.1 true c hc l hl
      · exact ihs hr.2 true c hc l hl

namespace Cof

/-- `∀ i. φ`, `i` the last variable. -/
def forall0 (φ : Cof (n + 1)) : Cof n := {p | p.IsK3 ∧ (Fin.snoc (α := fun _ => M4) p a) ∈ φ}

theorem snoc_isK3 {p : Pt n} (hp : p.IsK3) {x : M4} (hx : M4.IsK3 x) :
    Pt.IsK3 (Fin.snoc (α := fun _ => M4) p x : Pt (n + 1)) := by
  intro j; refine Fin.lastCases ?_ (fun i => ?_) j
  · simp [hx]
  · simp [hp i]

theorem forall0_restr (φ : Cof (n + 1)) (h : Hom k n) :
    (forall0 φ).restr h = forall0 (φ.restr (Hom.lift h)) := by
  ext p
  simp only [forall0, restr, Set.mem_setOf_eq, Hom.app_lift]
  constructor
  · rintro ⟨hp, -, hq⟩; refine ⟨hp, snoc_isK3 hp (by simp [M4.IsK3]), ?_⟩
    simpa [Fin.init_snoc] using hq
  · rintro ⟨hp, -, hq⟩; refine ⟨hp, h.app_isK3 hp, ?_⟩
    simpa [Fin.init_snoc] using hq

end Cof

theorem snoc_ext_lt {p : Pt n} {x : M4} {i : ℕ} (hi : i < n) :
    Pt.ext (Fin.snoc (α := fun _ => M4) p x : Pt (n + 1)) i = p.ext i := by
  simp only [Pt.ext, show i < n + 1 by omega, hi, dif_pos]
  have : (⟨i, by omega⟩ : Fin (n + 1)) = Fin.castSucc ⟨i, hi⟩ := rfl
  rw [this, Fin.snoc_castSucc]

theorem snoc_ext_last {p : Pt n} {x : M4} : Pt.ext (Fin.snoc (α := fun _ => M4) p x : Pt (n + 1)) n = x := by
  simp only [Pt.ext, show n < n + 1 by omega, dif_pos]
  have : (⟨n, by omega⟩ : Fin (n + 1)) = Fin.last n := rfl
  rw [this, Fin.snoc_last]

theorem litHolds_a_ne {p : Pt n} {d : Bool} : ¬ LitHolds (Pt.ext (Fin.snoc (α := fun _ => M4) p a : Pt (n + 1))) (n, d) := by
  simp only [LitHolds, snoc_ext_last]; cases d <;> simp

/-- A clause of a scoped term that holds at `(p, a)` does not mention the last variable, and
holds at `(p, x)` for every `x`. -/
theorem clause_snoc {c : Face} (hc : ∀ l ∈ c, l.1 < n + 1) {p : Pt n}
    (h : ∀ l ∈ c, LitHolds (Pt.ext (Fin.snoc (α := fun _ => M4) p a : Pt (n + 1))) l) :
    (∀ l ∈ c, l.1 < n) ∧ ∀ x : M4, ∀ l ∈ c, LitHolds (Pt.ext (Fin.snoc (α := fun _ => M4) p x : Pt (n + 1))) l := by
  have hlt : ∀ l ∈ c, l.1 < n := by
    intro l hl
    rcases Nat.lt_succ_iff_lt_or_eq.1 (hc l hl) with h1 | h1
    · exact h1
    · obtain ⟨i, d⟩ := l; simp only at h1; subst h1; exact absurd (h _ hl) litHolds_a_ne
  refine ⟨hlt, fun x l hl => ?_⟩
  have := h l hl
  obtain ⟨i, d⟩ := l
  simp only [LitHolds] at this ⊢
  rwa [snoc_ext_lt (hlt _ hl)] at this ⊢

namespace Cof

/-- `∀ i. φ` entails `φ` at every value of `i`. -/
theorem forall0_holds_snoc {φ : Cof (n + 1)} (hφ : φ.IsCof) {g : Hom k n}
    (hg : ((forall0 φ).restr g).holds) (r : DM k) : (φ.restr (Hom.snoc g r)).holds := by
  obtain ⟨G, rfl⟩ := hφ
  obtain ⟨t, ht, hG⟩ := G.defn
  obtain ⟨-, -, hq⟩ := hg
  obtain ⟨hqK, hGq⟩ := hq
  set q := g.app (Pt.allA k)
  have hqK3 : q.IsK3 := g.app_isK3 (Pt.allA_isK3 k)
  rw [hG, eval_eq_one_iff_faces (Pt.ext_isK3 hqK)] at hGq
  obtain ⟨c, hc, hcl⟩ := hGq
  have hcs : ∀ l ∈ c, l.1 < n + 1 := dnf_scoped ht true c (List.mem_filter.1 hc).1
  have hrK : M4.IsK3 (r.fn (Pt.allA k)) := r.defn.isK3 (Pt.allA_isK3 k)
  refine ⟨Pt.allA_isK3 k, ?_⟩
  rw [Hom.app_snoc]
  refine ⟨snoc_isK3 hqK3 hrK, ?_⟩
  rw [hG, eval_eq_one_iff_faces (Pt.ext_isK3 (snoc_isK3 hqK3 hrK))]
  exact ⟨c, hc, (clause_snoc hcs hcl).2 _⟩

end Cof

theorem scoped_ofFace {α : Face} (h : ∀ l ∈ α, l.1 < n) : (I.ofFace α).Scoped n := by
  induction α with
  | nil => trivial
  | cons l α ih =>
    obtain ⟨i, d⟩ := l
    refine ⟨?_, ih fun l hl => h l (List.mem_cons_of_mem _ hl)⟩
    have := h _ List.mem_cons_self
    cases d <;> exact this

theorem scoped_ofFaces {cs : List Face} (h : ∀ c ∈ cs, ∀ l ∈ c, l.1 < n) : (I.ofFaces cs).Scoped n := by
  induction cs with
  | nil => trivial
  | cons c cs ih => exact ⟨scoped_ofFace (h c List.mem_cons_self), ih fun c hc => h c (List.mem_cons_of_mem _ hc)⟩

namespace Cof

theorem IsCof.forall0 {φ : Cof (n + 1)} (hφ : φ.IsCof) : (forall0 φ).IsCof := by
  obtain ⟨G, rfl⟩ := hφ
  obtain ⟨t, ht, hG⟩ := G.defn
  set cs := t.faces.filter fun c => c.all (·.1 != n)
  have hcs : ∀ c ∈ cs, ∀ l ∈ c, l.1 < n := by
    intro c hc l hl
    obtain ⟨hc1, hc2⟩ := List.mem_filter.1 hc
    have h1 := dnf_scoped ht true c (List.mem_filter.1 hc1).1 l hl
    have h2 : l.1 ≠ n := by
      have := List.all_eq_true.1 hc2 l hl
      simpa using this
    omega
  refine ⟨DM.ofTerm (I.ofFaces cs) (scoped_ofFaces hcs), ?_⟩
  ext p
  simp only [forall0, DM.face, Set.mem_setOf_eq, DM.ofTerm]
  constructor
  · rintro ⟨hp, hq, hGq⟩
    refine ⟨hp, ?_⟩
    rw [hG, eval_eq_one_iff_faces (Pt.ext_isK3 hq)] at hGq
    obtain ⟨c, hc, hcl⟩ := hGq
    have hcs' : ∀ l ∈ c, l.1 < n + 1 := dnf_scoped ht true c (List.mem_filter.1 hc).1
    obtain ⟨hlt, -⟩ := clause_snoc hcs' hcl
    rw [eval_ofFaces, dnfVal_eq_one_K3 (Pt.ext_isK3 hp)]
    refine ⟨c, List.mem_filter.2 ⟨hc, List.all_eq_true.2 fun l hl => by simpa using (hlt l hl).ne⟩, fun l hl => ?_⟩
    have := hcl l hl
    obtain ⟨i, d⟩ := l
    simp only [LitHolds] at this ⊢
    rwa [snoc_ext_lt (hlt _ hl)] at this
  · rintro ⟨hp, hev⟩
    rw [eval_ofFaces, dnfVal_eq_one_K3 (Pt.ext_isK3 hp)] at hev
    obtain ⟨c, hc, hcl⟩ := hev
    have hq := snoc_isK3 hp (show M4.IsK3 a by simp [M4.IsK3])
    refine ⟨hp, hq, ?_⟩
    rw [hG, eval_eq_one_iff_faces (Pt.ext_isK3 hq)]
    refine ⟨c, (List.mem_filter.1 hc).1, fun l hl => ?_⟩
    have := hcl l hl
    obtain ⟨i, d⟩ := l
    simp only [LitHolds] at this ⊢
    rwa [snoc_ext_lt (hcs c hc _ hl)]

end Cof

end Model
