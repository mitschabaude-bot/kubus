import Model.DataCode
import Model.SmallBasic
import Mathlib.SetTheory.Cardinal.Regular
import Mathlib.Logic.Equiv.List

/-!
# Inductive types: the element sets are small

The elements of an inductive type are generated in `ω₁` stages, each a small set: a stage
consists of the constructor values with arguments from the earlier stages (and from the small
argument types), the formal compositions with tube and base from earlier stages, and the
restrictions of earlier elements. Every element appears at a countable stage (a formal
composition has countably many tube values), so the union of the stages below `ω₁` bounds the
elements, and it is small.
-/

set_option autoImplicit false

universe w

namespace Model

open ZFSet KubusCore Cardinal

noncomputable section

attribute [local instance] Classical.propDecidable

variable {l k m n : ℕ}

/-! ### `ω₁` -/

/-- The first uncountable ordinal. -/
abbrev omega1 : Ordinal.{0} := (aleph 1).ord

theorem iSup_lt_omega1 {ι : Type} [Countable ι] (f : ι → Ordinal.{0}) (hf : ∀ i, f i < omega1) :
    ⨆ i, f i < omega1 := by
  refine Ordinal.iSup_lt_of_lt_cof ?_ hf
  rw [isRegular_aleph_one.cof_ord]
  exact (mk_le_aleph0 (α := ι)).trans_lt aleph0_lt_aleph_one

theorem countable_Iio_of_lt_omega1 {α : Ordinal.{0}} (hα : α < omega1) : Countable (Set.Iio α) := by
  rw [← mk_le_aleph0_iff, Cardinal.mk_Iio_ordinal, Cardinal.lift_le_aleph0]
  have h1 : α.card < aleph 1 := Cardinal.lt_ord.1 hα
  rw [← Cardinal.succ_aleph0] at h1
  exact Order.lt_succ_iff.1 h1

/-! ### Valid argument lists -/

section pref

variable (Θ : SData m) (Y : (n : ℕ) → Hom n m → V) (n : ℕ) (g : Hom n m) (c : ℕ) (C : Ctor)

/-- The set the argument `i` of constructor `c` ranges over, after the arguments `pre`. -/
def argSet (pre : List V) (i : ℕ) : V :=
  if C.isRec i then Y n g else El (Θ.ty c i n g pre) (Hom.id n)

/-- Valid argument lists of length `j`. -/
def VPref (j : ℕ) : Type 6 :=
  {p : List V // p.length = j ∧ ∀ i (hi : i < p.length), p[i] ∈ argSet Θ Y n g c C (p.take i) i}

variable {Θ Y n g c C}

theorem vpref_mem_Vt (hl : l ≤ 4) (hY : ∀ n g, Y n g ∈ Vt l)
    (hty : ∀ c i n g pre, (∀ a ∈ pre, a ∈ Vt l) → Θ.ty c i n g pre ∈ Vt l) {p : List V}
    (hp : ∀ i (hi : i < p.length), p[i] ∈ argSet Θ Y n g c C (p.take i) i) :
    ∀ i (hi : i < p.length), p[i] ∈ Vt l := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    refine Vt_trans l ?_ (hp i hi)
    unfold argSet; split
    · exact hY n g
    · refine El_mem_Vt hl (hty _ _ _ _ _ fun a ha => ?_) _
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ha
      rw [List.getElem_take]
      exact ih j (by simp at hj; omega) _

theorem argSet_mem_Vt (hl : l ≤ 4) (hY : ∀ n g, Y n g ∈ Vt l)
    (hty : ∀ c i n g pre, (∀ a ∈ pre, a ∈ Vt l) → Θ.ty c i n g pre ∈ Vt l) {pre : List V}
    (hpre : ∀ a ∈ pre, a ∈ Vt l) (i : ℕ) : argSet Θ Y n g c C pre i ∈ Vt l := by
  unfold argSet; split
  · exact hY n g
  · exact El_mem_Vt hl (hty _ _ _ _ _ hpre) _

instance vpref_small5 : ∀ j, Small.{5} (VPref Θ Y n g c C j)
  | 0 => by
    have : Subsingleton (VPref Θ Y n g c C 0) := ⟨fun a b => Subtype.ext (by
      rw [List.length_eq_zero_iff.1 a.2.1, List.length_eq_zero_iff.1 b.2.1])⟩
    infer_instance
  | j + 1 => by
    haveI := vpref_small5 j
    let U : V := ⋃ p : VPref Θ Y n g c C j, argSet Θ Y n g c C p.1 j
    let ι : VPref Θ Y n g c C (j + 1) → List V × (U : Type 6) :=
      fun p => (p.1.take j, ⟨p.1[j]'(by rw [p.2.1]; omega), ZFSet.mem_iUnion.2 ⟨⟨p.1.take j, by simp [p.2.1],
        fun i hi => by
          have hi' : i < p.1.length := by simp at hi; omega
          have := p.2.2 i hi'
          simp only [List.getElem_take, List.take_take]
          rwa [Nat.min_eq_left (by simp at hi; omega)]⟩, p.2.2 j (by rw [p.2.1]; omega)⟩⟩)
    let ι' : VPref Θ Y n g c C (j + 1) → (Set.range fun p : VPref Θ Y n g c C j => p.1) × (U : Type 6) :=
      fun p => (⟨p.1.take j, ⟨⟨p.1.take j, by simp [p.2.1], fun i hi => by
          have hi' : i < p.1.length := by simp at hi; omega
          have := p.2.2 i hi'
          simp only [List.getElem_take, List.take_take]
          rwa [Nat.min_eq_left (by simp at hi; omega)]⟩, rfl⟩⟩, (ι p).2)
    have hι : Function.Injective ι' := by
      intro p q hpq
      simp only [ι', ι, Prod.mk.injEq, Subtype.mk.injEq] at hpq
      obtain ⟨h1, h2⟩ := hpq
      apply Subtype.ext
      have hp : p.1 = p.1.take j ++ [p.1[j]'(by rw [p.2.1]; omega)] := by
        rw [← List.take_succ_eq_append_getElem, List.take_of_length_le (by rw [p.2.1])]
      have hq : q.1 = q.1.take j ++ [q.1[j]'(by rw [q.2.1]; omega)] := by
        rw [← List.take_succ_eq_append_getElem, List.take_of_length_le (by rw [q.2.1])]
      rw [hp, hq, h1, h2]
    exact small_of_injective hι

theorem vpref_small (hl : l ≤ 4) (hY : ∀ n g, Y n g ∈ Vt l)
    (hty : ∀ c i n g pre, (∀ a ∈ pre, a ∈ Vt l) → Θ.ty c i n g pre ∈ Vt l) :
    ∀ j, Small.{5} (VPref Θ Y n g c C j) ∧ IsSmallAt l (VPref Θ Y n g c C j) := by
  intro j
  induction j with
  | zero =>
    have : Subsingleton (VPref Θ Y n g c C 0) := ⟨fun a b => Subtype.ext (by
      rw [List.length_eq_zero_iff.1 a.2.1, List.length_eq_zero_iff.1 b.2.1])⟩
    exact ⟨inferInstance, (IsSmallAt.of_countable (α := Unit)).of_surjective (f := fun _ => ⟨[], rfl, by simp⟩)
      fun p => ⟨(), Subsingleton.elim _ _⟩⟩
  | succ j ih =>
    obtain ⟨ih5, ihl⟩ := ih
    haveI := ih5
    have hset : ∀ p : VPref Θ Y n g c C j, argSet Θ Y n g c C p.1 j ∈ Vt l := fun p =>
      argSet_mem_Vt hl hY hty (fun a ha => by
        obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
        exact vpref_mem_Vt hl hY hty p.2.2 i hi) j
    let U : V := ⋃ p : VPref Θ Y n g c C j, argSet Θ Y n g c C p.1 j
    have hU : U ∈ Vt l := iUnion_mem_Vt ihl hset hl
    let ι : VPref Θ Y n g c C (j + 1) → VPref Θ Y n g c C j × (U : Type 6) :=
      fun p => (⟨p.1.take j, by simp [p.2.1], fun i hi => by
          have hi' : i < p.1.length := by simp at hi; omega
          have := p.2.2 i hi'
          simp only [List.getElem_take, List.take_take]
          rwa [Nat.min_eq_left (by simp at hi; omega)]⟩,
        ⟨p.1[j]'(by rw [p.2.1]; omega), ZFSet.mem_iUnion.2 ⟨⟨p.1.take j, by simp [p.2.1], fun i hi => by
          have hi' : i < p.1.length := by simp at hi; omega
          have := p.2.2 i hi'
          simp only [List.getElem_take, List.take_take]
          rwa [Nat.min_eq_left (by simp at hi; omega)]⟩, p.2.2 j (by rw [p.2.1]; omega)⟩⟩)
    have hι : Function.Injective ι := by
      intro p q hpq
      simp only [ι, Prod.mk.injEq, Subtype.mk.injEq] at hpq
      obtain ⟨h1, h2⟩ := hpq
      apply Subtype.ext
      have hp : p.1 = p.1.take j ++ [p.1[j]'(by rw [p.2.1]; omega)] := by
        rw [← List.take_succ_eq_append_getElem, List.take_of_length_le (by rw [p.2.1])]
      have hq : q.1 = q.1.take j ++ [q.1[j]'(by rw [q.2.1]; omega)] := by
        rw [← List.take_succ_eq_append_getElem, List.take_of_length_le (by rw [q.2.1])]
      have e1 : p.1.take j = q.1.take j := congrArg Subtype.val h1
      rw [hp, hq, e1, h2]
    exact ⟨small_of_injective hι,
      (ihl.prod (isSmallAt_of_mem_Vt hU)).of_injective hι⟩

end pref

/-! ### Closure of `Vt l` under the element constructions -/

theorem vlist_mem_Vt (hl : l ≤ 4) : ∀ {as : List V}, (∀ a ∈ as, a ∈ Vt l) → vlist as ∈ Vt l
  | [], _ => empty_mem_Vt hl
  | a :: as, h => pair_mem_Vt (h a List.mem_cons_self) (vlist_mem_Vt hl fun b hb => h b (List.mem_cons_of_mem _ hb))

theorem junkV_mem_Vt (hl : l ≤ 4) : junkV n ∈ Vt l := mkKV_mem_Vt hl fun _ _ => empty_mem_Vt hl

theorem evalBnd_mem_Vt (hl : l ≤ 4) {conF : ℕ → List V → List (DM n) → V}
    (hc : ∀ c as rs, (∀ a ∈ as, a ∈ Vt l) → conF c as rs ∈ Vt l) {args : List V} (hargs : ∀ a ∈ args, a ∈ Vt l)
    (rs : List (DM n)) : ∀ b : Tm,
    evalBnd conF args rs b ∈ Vt l ∧ ∀ a ∈ evalBndList conF args rs b, a ∈ Vt l := by
  intro b
  induction b with
  | var j =>
    refine ⟨?_, by simp [evalBndList]⟩
    simp only [evalBnd]
    refine res_mem_Vt' hl ?_ _
    rw [List.getD_eq_getElem?_getD]
    cases h : args.reverse[j]? with
    | none => exact empty_mem_Vt hl
    | some x => exact hargs x (List.mem_reverse.1 (List.mem_of_getElem? h))
  | con d c ps as rs' _ ihas =>
    exact ⟨hc _ _ _ ihas.2, by simp [evalBndList]⟩
  | tcons a as iha ihas =>
    refine ⟨by simp only [evalBnd]; exact junkV_mem_Vt hl, ?_⟩
    simp only [evalBndList, List.mem_cons]
    rintro x (rfl | hx)
    · exact iha.1
    · exact ihas.2 x hx
  | _ => exact ⟨by simp only [evalBnd]; exact junkV_mem_Vt hl, by simp [evalBndList]⟩

theorem conV_mem_Vt (hl : l ≤ 4) (ctors : List Ctor) : ∀ (c : ℕ) {n : ℕ} {args : List V} (rs : List (DM n)),
    (∀ a ∈ args, a ∈ Vt l) → conV ctors n c args rs ∈ Vt l := by
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ih =>
    intro n args rs hargs
    rw [conV_eq]
    refine mkKV_mem_Vt hl fun k f => ?_
    split
    · refine dat_mem_Vt hl (evalBnd_mem_Vt hl (fun c' as rs' has => ?_) hargs rs _).1 f
      split
      · exact ih c' ‹_› rs' has
      · exact junkV_mem_Vt hl
    · refine tagZ_mem_Vt (pair_mem_Vt (natZ_mem_Vt hl _) (pair_mem_Vt (vlist_mem_Vt hl ?_) (vlist_mem_Vt hl ?_)))
      · simp only [List.mem_map]; rintro _ ⟨a, ha, rfl⟩; exact res_mem_Vt' hl (hargs a ha) f
      · simp only [List.mem_map]; rintro _ ⟨r, -, rfl⟩; exact enc_mem_Vt hl _

theorem hcV_mem_Vt (hl : l ≤ 4) {φ : Cof n} {u : Tube n} {a : V}
    (hu : ∀ n' (h : Hom n' n) r, (φ.restr h).holds → u n' h r ∈ Vt l) (ha : a ∈ Vt l) : hcV n φ u a ∈ Vt l := by
  refine mkKV_mem_Vt hl fun k f => ?_
  split
  · exact here_mem_Vt hl (hu k f _ ‹_›)
  · refine tagZ_mem_Vt (pair_mem_Vt (enc_mem_Vt hl _) (pair_mem_Vt (tubeZ_mem_Vt hl fun n' h r hh => ?_)
      (res_mem_Vt' hl ha f)))
    rw [Cof.restr_restr] at hh
    exact hu _ _ _ hh

/-! ### The stages -/

section stages

variable (Θ : SData m)

/-- Interval argument lists of a given length. -/
abbrev RsT (n d : ℕ) := {rs : List (DM n) // rs.length = d}

/-- The constructor values with arguments from `Y`. -/
def conPart (Y : (n : ℕ) → Hom n m → V) (n : ℕ) (g : Hom n m) : V :=
  ⋃ c : Fin Θ.ctors.length,
    ZFSet.range fun x : VPref Θ Y n g c Θ.ctors[c] Θ.ctors[c].args.length × RsT n Θ.ctors[c].dims =>
      conV Θ.ctors n c x.1.1 x.2.1

/-- The inputs of a formal composition with tube values and base from `Y`. -/
abbrev HcInY (Y : (n : ℕ) → Hom n m → V) (n : ℕ) (g : Hom n m) :=
  (_ : Cof n) × ((y : TubeDom n) → ↥(insert ∅ (Y y.1 (g.comp y.2.1)))) × ↥(Y n g)

/-- The formal compositions with tube and base from `Y`. -/
def hcPart (Y : (n : ℕ) → Hom n m → V) (n : ℕ) (g : Hom n m) : V :=
  ZFSet.range fun x : HcInY Y n g => hcV n x.1 (fun n' h r => (x.2.1 ⟨n', h, r⟩).1) x.2.2.1

/-- One stage. -/
def stepY (Y : (n : ℕ) → Hom n m → V) (n : ℕ) (g : Hom n m) : V :=
  conPart Θ Y n g ∪ hcPart Y n g

/-- The stages of the construction of the elements. -/
def stages : Ordinal.{0} → (n : ℕ) → Hom n m → V :=
  WellFoundedLT.fix fun α ih => stepY Θ fun n g => ⋃ β : Set.Iio α, ih β.1 β.2 n g

/-- The union of the countable stages: a small set containing all elements. -/
def dataBound (n : ℕ) (g : Hom n m) : V := ⋃ α : Set.Iio omega1, stages Θ α.1 n g

theorem stages_eq (α : Ordinal.{0}) :
    stages Θ α = stepY Θ fun n g => ⋃ β : Set.Iio α, stages Θ β.1 n g := by
  rw [stages, WellFoundedLT.fix_eq]

end stages

section bound

variable {Θ : SData m} (hl : l ≤ 4)
  (hty : ∀ c i n g pre, (∀ a ∈ pre, a ∈ Vt l) → Θ.ty c i n g pre ∈ Vt l)
include hl hty

omit hty in
theorem union_mem_Vt' {x y : V} (hx : x ∈ Vt l) (hy : y ∈ Vt l) : x ∪ y ∈ Vt l := by
  refine mem_Vt_of hl (fun z hz => ?_) ?_
  · rcases ZFSet.mem_union.1 hz with h | h
    · exact Vt_trans l hx h
    · exact Vt_trans l hy h
  · refine ((isSmallAt_of_mem_Vt hx).sum (isSmallAt_of_mem_Vt hy)).of_surjective
      (f := Sum.elim (fun a => ⟨a.1, ZFSet.mem_union.2 (Or.inl a.2)⟩) (fun a => ⟨a.1, ZFSet.mem_union.2 (Or.inr a.2)⟩)) ?_
    rintro ⟨z, hz⟩
    rcases ZFSet.mem_union.1 hz with h | h
    · exact ⟨Sum.inl ⟨z, h⟩, rfl⟩
    · exact ⟨Sum.inr ⟨z, h⟩, rfl⟩

theorem stepY_mem_Vt {Y : (n : ℕ) → Hom n m → V} (hY : ∀ n g, Y n g ∈ Vt l) (n : ℕ) (g : Hom n m) :
    stepY Θ Y n g ∈ Vt l := by
  refine union_mem_Vt' hl ?_ ?_
  · refine iUnion_mem_Vt IsSmallAt.of_countable (fun c => ?_) hl
    refine range_mem_Vt' ((vpref_small hl hY hty _).2.prod IsSmallAt.of_countable) (fun x => ?_) hl
    exact conV_mem_Vt hl _ _ _ fun a ha => by
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
      exact vpref_mem_Vt hl hY hty x.1.2.2 i hi
  · refine range_mem_Vt' (IsSmallAt.of_countable.sigma fun _ =>
      (IsSmallAt.pi IsSmallAt.of_countable fun (y : TubeDom n) =>
        isSmallAt_of_mem_Vt (insert_mem_Vt (empty_mem_Vt hl) (hY y.1 (g.comp y.2.1)))).prod
      (isSmallAt_of_mem_Vt (hY n g))) (fun x => hcV_mem_Vt hl (fun n' h r _ => ?_) (Vt_trans l (hY n g) x.2.2.2)) hl
    exact Vt_trans l (insert_mem_Vt (empty_mem_Vt hl) (hY _ _)) (x.2.1 ⟨n', h, r⟩).2

theorem stages_mem_Vt : ∀ α < omega1, ∀ n (g : Hom n m), stages Θ α n g ∈ Vt l := by
  intro α
  induction α using WellFoundedLT.induction with
  | _ α ih =>
    intro hα n g
    rw [stages_eq]
    refine stepY_mem_Vt hl hty (fun n' g' => ?_) n g
    haveI := countable_Iio_of_lt_omega1 hα
    exact iUnion_mem_Vt IsSmallAt.of_countable (fun β => ih β.1 β.2 (β.2.trans hα) n' g') hl

theorem dataBound_mem_Vt (n : ℕ) (g : Hom n m) : dataBound Θ n g ∈ Vt l := by
  refine iUnion_mem_Vt IsSmallAt.of_small0 (fun α => stages_mem_Vt hl hty α.1 α.2 n g) hl

end bound

theorem succ_lt_omega1 {α : Ordinal.{0}} (h : α < omega1) : α + 1 < omega1 := by
  rw [← Order.succ_eq_add_one]
  exact (Cardinal.isSuccLimit_ord (aleph0_le_aleph 1)).succ_lt h

theorem omega1_pos : (0 : Ordinal.{0}) < omega1 := Cardinal.ord_pos.2 (Cardinal.aleph_pos 1)

theorem mem_iUnion_Iio {f : Ordinal.{0} → V} {α β : Ordinal.{0}} (hβ : β < α) {v : V} (hv : v ∈ f β) :
    v ∈ ⋃ γ : Set.Iio α, f γ.1 :=
  ZFSet.mem_iUnion.2 ⟨⟨β, hβ⟩, hv⟩

/-- Every element appears at a countable stage. -/
theorem delem_stage {Θ : SData m} {n : ℕ} {g : Hom n m} {v : V} (h : DElem Θ n g v) :
    ∃ α < omega1, v ∈ stages Θ α n g := by
  induction h with
  | @con n g c C args rs hC hlen hrs hrec hpt ihrec =>
    have hcl : c < Θ.ctors.length := (List.getElem?_eq_some_iff.1 hC).1
    have hCe : Θ.ctors[c] = C := (List.getElem?_eq_some_iff.1 hC).2
    let f : Fin args.length → Ordinal.{0} := fun j =>
      if hj : C.isRec j = true then Classical.choose (ihrec j args[j] (List.getElem?_eq_getElem j.2) hj) else 0
    have hf : ∀ j, f j < omega1 := fun j => by
      simp only [f]; split
      · exact (Classical.choose_spec (ihrec j args[j] (List.getElem?_eq_getElem j.2) ‹_›)).1
      · exact omega1_pos
    have hα := iSup_lt_omega1 f hf
    refine ⟨(⨆ j, f j) + 1, succ_lt_omega1 hα, ?_⟩
    rw [stages_eq]
    refine ZFSet.mem_union.2 (Or.inl (ZFSet.mem_iUnion.2 ⟨⟨c, hcl⟩, ?_⟩))
    subst hCe
    refine ZFSet.mem_range.2 ⟨(⟨args, hlen, fun i hi => ?_⟩, ⟨rs, hrs⟩), rfl⟩
    unfold argSet
    split
    · rename_i hrec'
      have hs := Classical.choose_spec (ihrec i args[i] (List.getElem?_eq_getElem hi) hrec')
      refine mem_iUnion_Iio (f := fun β => stages Θ β n g) (lt_of_le_of_lt ?_ (Order.lt_add_one_iff.2 le_rfl)) hs.2
      refine le_trans (le_of_eq ?_) (Ordinal.le_iSup f ⟨i, hi⟩)
      show _ = f ⟨i, hi⟩
      simp only [f]; split
      · rfl
      · contradiction
    · rename_i hnr
      exact hpt i args[i] (List.getElem?_eq_getElem hi) (by simpa using hnr)
  | @hcomp n g φ u a hφ ha hu hcoh hbase iha ihu =>
    let f : TubeDom n → Ordinal.{0} := fun y =>
      if hy : (φ.restr y.2.1).holds then Classical.choose (ihu y.1 y.2.1 y.2.2 hy) else 0
    have hf : ∀ y, f y < omega1 := fun y => by
      simp only [f]; split
      · exact (Classical.choose_spec (ihu y.1 y.2.1 y.2.2 ‹_›)).1
      · exact omega1_pos
    obtain ⟨αa, hαa, haα⟩ := iha
    have hα : max αa (⨆ y, f y) < omega1 := max_lt hαa (iSup_lt_omega1 f hf)
    refine ⟨max αa (⨆ y, f y) + 1, succ_lt_omega1 hα, ?_⟩
    have hlt : ∀ {β}, β ≤ max αa (⨆ y, f y) → β < max αa (⨆ y, f y) + 1 := fun h =>
      lt_of_le_of_lt h (Order.lt_add_one_iff.2 le_rfl)
    rw [stages_eq]
    refine ZFSet.mem_union.2 (Or.inr ?_)
    let tube : (y : TubeDom n) → ↥(insert ∅ ((fun n' g' => ZFSet.iUnion (fun β : Set.Iio (max αa (⨆ y, f y) + 1) =>
        stages Θ β.1 n' g')) y.1 (g.comp y.2.1))) := fun y =>
      if hy : (φ.restr y.2.1).holds then
        ⟨u y.1 y.2.1 y.2.2, ZFSet.mem_insert_of_mem _ (mem_iUnion_Iio (f := fun β => stages Θ β y.1 (g.comp y.2.1))
          (hlt (le_trans (le_of_eq (by simp only [f, dif_pos hy])) (le_trans (Ordinal.le_iSup f y) (le_max_right _ _))))
          (Classical.choose_spec (ihu y.1 y.2.1 y.2.2 hy)).2)⟩
      else ⟨∅, ZFSet.mem_insert _ _⟩
    refine ZFSet.mem_range.2 ⟨⟨φ, tube, ⟨a, mem_iUnion_Iio (f := fun β => stages Θ β n g) (hlt (le_max_left _ _)) haα⟩⟩, ?_⟩
    exact hcV_congr a fun n' h r hh => by simp only [tube, dif_pos hh]

theorem delem_mem_bound {Θ : SData m} {n : ℕ} {g : Hom n m} {v : V} (h : DElem Θ n g v) :
    v ∈ dataBound Θ n g := by
  obtain ⟨α, hα, hv⟩ := delem_stage h
  exact ZFSet.mem_iUnion.2 ⟨⟨α, hα⟩, hv⟩


end

end Model
