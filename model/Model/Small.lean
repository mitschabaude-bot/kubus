import Model.Univ
import Mathlib.Data.Countable.Small

/-!
# Smallness of codes

`Vt l` (the embedded `ZFSet.{l}`) is closed under the constructions of the model: a set is in
`Vt l` iff its members are and it is `l`-small (`mem_Vt_of`, `isSmallAt_of_mem_Vt`). The Kan
operations of a code are lookups in its graphs, so their results lie below the code; the element
sets and graphs are built by pairing, ranges over small index types and separation.
-/

set_option autoImplicit false

universe w w'

namespace Model

open ZFSet

noncomputable section

attribute [local instance] Classical.propDecidable

variable {l k m n : ℕ}

/-! ### Smallness of index types -/

theorem IsSmallAt.of_small0 {α : Type w} [Small.{0} α] : IsSmallAt l α := by
  rcases l with _ | _ | _ | _ | _ | l <;> simp only [IsSmallAt]
  · infer_instance
  · exact (small_lift α : Small.{max 0 1} α)
  · exact (small_lift α : Small.{max 0 2} α)
  · exact (small_lift α : Small.{max 0 3} α)
  · exact (small_lift α : Small.{max 0 4} α)

theorem IsSmallAt.of_countable {α : Type w} [Countable α] : IsSmallAt l α :=
  haveI : Small.{0} α := Countable.toSmall α
  IsSmallAt.of_small0

theorem IsSmallAt.of_surjective {α : Type w} {β : Type w'} (h : IsSmallAt l α) {f : α → β}
    (hf : Function.Surjective f) : IsSmallAt l β := by
  rcases l with _ | _ | _ | _ | _ | l <;> simp only [IsSmallAt] at h ⊢ <;>
    first | exact small_of_surjective hf | trivial

theorem IsSmallAt.of_injective {α : Type w} {β : Type w'} (h : IsSmallAt l β) {f : α → β}
    (hf : Function.Injective f) : IsSmallAt l α := by
  rcases l with _ | _ | _ | _ | _ | l <;> simp only [IsSmallAt] at h ⊢ <;>
    first | exact small_of_injective hf | trivial

theorem IsSmallAt.sigma {α : Type w} {β : α → Type w'} (hα : IsSmallAt l α) (hβ : ∀ a, IsSmallAt l (β a)) :
    IsSmallAt l (Σ a, β a) := by
  rcases l with _ | _ | _ | _ | _ | l <;> simp only [IsSmallAt] at hα hβ ⊢ <;>
    first | (haveI := hα; haveI := hβ; infer_instance) | trivial

theorem IsSmallAt.pi {α : Type w} {β : α → Type w'} (hα : IsSmallAt l α) (hβ : ∀ a, IsSmallAt l (β a)) :
    IsSmallAt l (∀ a, β a) := by
  rcases l with _ | _ | _ | _ | _ | l <;> simp only [IsSmallAt] at hα hβ ⊢ <;>
    first | (haveI := hα; haveI := hβ; infer_instance) | trivial

theorem IsSmallAt.prod {α : Type w} {β : Type w'} (hα : IsSmallAt l α) (hβ : IsSmallAt l β) :
    IsSmallAt l (α × β) := by
  rcases l with _ | _ | _ | _ | _ | l <;> simp only [IsSmallAt] at hα hβ ⊢ <;>
    first | (haveI := hα; haveI := hβ; infer_instance) | trivial

theorem IsSmallAt.sum {α : Type w} {β : Type w'} (hα : IsSmallAt l α) (hβ : IsSmallAt l β) :
    IsSmallAt l (α ⊕ β) := by
  rcases l with _ | _ | _ | _ | _ | l <;> simp only [IsSmallAt] at hα hβ ⊢ <;>
    first | (haveI := hα; haveI := hβ; infer_instance) | trivial

theorem IsSmallAt.option {α : Type w} (hα : IsSmallAt l α) : IsSmallAt l (Option α) :=
  (hα.sum (IsSmallAt.of_countable (α := Unit))).of_surjective (f := Sum.elim some fun _ => none) (by
    intro o; cases o with
    | none => exact ⟨Sum.inr (), rfl⟩
    | some a => exact ⟨Sum.inl a, rfl⟩)

theorem IsSmallAt.set {α : Type w} (hα : IsSmallAt l α) : IsSmallAt l (Set α) := by
  rcases l with _ | _ | _ | _ | _ | l <;> simp only [IsSmallAt] at hα ⊢ <;>
    first | (haveI := hα; infer_instance) | trivial

theorem IsSmallAt.subtype {α : Type w} (hα : IsSmallAt l α) (p : α → Prop) : IsSmallAt l {a // p a} :=
  hα.of_injective Subtype.val_injective

/-! ### The characterisation of `Vt l` -/

theorem le_of_mem_Vt {x : V} (hx : x ∈ Vt l) : l ≤ 4 := by
  by_contra h
  obtain ⟨l, rfl⟩ : ∃ l', l = l' + 5 := ⟨l - 5, by omega⟩
  exact ZFSet.notMem_empty _ hx

theorem Vt_mem_trans {x y : V} (hx : x ∈ Vt l) (hy : y ∈ x) : y ∈ Vt l := Vt_trans l hx hy

theorem Vt_of_below {x c : V} (h : Below x c) (hc : c ∈ Vt l) : x ∈ Vt l := by
  induction h with
  | single h => exact Vt_trans l hc h
  | tail _ h ih => exact ih (Vt_trans l hc h)

theorem range_val (x : V) : ZFSet.range (fun y : x => y.1) = x := by
  ext z; simp

theorem mem_Vt_of (hl : l ≤ 4) {x : V} (hmem : ∀ y ∈ x, y ∈ Vt l) (hs : IsSmallAt l x) : x ∈ Vt l := by
  rw [← range_val x]
  exact range_mem_Vt l hs _ (fun y => hmem y.1 y.2) hl

theorem isSmallAt_embedSet.{u} {x : ZFSet.{max (u + 1) 5}} (hx : x ∈ embedSet.{u, 5}) : Small.{u} x := by
  obtain ⟨z, rfl⟩ := mem_embedSet.1 hx
  have hf : Function.Surjective (fun w : z => (⟨liftZ.{u, 5} w.1, mem_liftZ.2 ⟨w.1, w.2, rfl⟩⟩ : liftZ.{u, 5} z)) := by
    rintro ⟨y, hy⟩
    obtain ⟨w, hw, rfl⟩ := mem_liftZ.1 hy
    exact ⟨⟨w, hw⟩, rfl⟩
  exact small_of_surjective hf

theorem isSmallAt_of_mem_Vt {x : V} (hx : x ∈ Vt l) : IsSmallAt l x := by
  rcases l with _ | _ | _ | _ | _ | l
  · exact isSmallAt_embedSet.{0} hx
  · exact isSmallAt_embedSet.{1} hx
  · exact isSmallAt_embedSet.{2} hx
  · exact isSmallAt_embedSet.{3} hx
  · exact isSmallAt_embedSet.{4} hx
  · trivial

/-! ### Closure properties -/

theorem empty_mem_Vt (hl : l ≤ 4) : (∅ : V) ∈ Vt l :=
  mem_Vt_of hl (fun y hy => absurd hy (ZFSet.notMem_empty _))
    ((IsSmallAt.of_countable (α := Empty)).of_surjective (f := fun e => e.elim)
      fun y => absurd y.2 (ZFSet.notMem_empty _))

theorem subset_mem_Vt {x y : V} (hy : y ∈ Vt l) (hxy : x ⊆ y) : x ∈ Vt l :=
  mem_Vt_of (le_of_mem_Vt hy) (fun z hz => Vt_trans l hy (hxy hz))
    ((isSmallAt_of_mem_Vt hy).of_injective (f := fun z : x => (⟨z.1, hxy z.2⟩ : y))
      fun a b h => Subtype.ext (by simpa using congrArg Subtype.val h))

theorem insert_mem_Vt {a x : V} (ha : a ∈ Vt l) (hx : x ∈ Vt l) : (insert a x : V) ∈ Vt l := by
  refine mem_Vt_of (le_of_mem_Vt hx) (fun y hy => ?_) ?_
  · rcases ZFSet.mem_insert_iff.1 hy with rfl | hy
    · exact ha
    · exact Vt_trans l hx hy
  · refine (isSmallAt_of_mem_Vt hx).option.of_surjective
      (f := fun o => match o with
        | none => (⟨a, ZFSet.mem_insert _ _⟩ : ((insert a x : V) : Type _))
        | some y => ⟨y.1, ZFSet.mem_insert_of_mem _ y.2⟩) ?_
    rintro ⟨y, hy⟩
    rcases ZFSet.mem_insert_iff.1 hy with rfl | hy
    · exact ⟨none, rfl⟩
    · exact ⟨some ⟨y, hy⟩, rfl⟩

theorem singleton_mem_Vt {a : V} (ha : a ∈ Vt l) : ({a} : V) ∈ Vt l := by
  have : ({a} : V) = insert a ∅ := by ext z; simp
  rw [this]; exact insert_mem_Vt ha (empty_mem_Vt (le_of_mem_Vt ha))

theorem pair_mem_Vt {a b : V} (ha : a ∈ Vt l) (hb : b ∈ Vt l) : pair a b ∈ Vt l := by
  show (insert ({a} : V) {insert a ({b} : V)} : V) ∈ Vt l
  exact insert_mem_Vt (singleton_mem_Vt ha) (singleton_mem_Vt (insert_mem_Vt ha (singleton_mem_Vt hb)))

theorem natZ_mem_Vt (hl : l ≤ 4) : ∀ n, natZ n ∈ Vt l
  | 0 => empty_mem_Vt hl
  | n + 1 => insert_mem_Vt (natZ_mem_Vt hl n) (natZ_mem_Vt hl n)

theorem enc_mem_Vt (hl : l ≤ 4) {α : Type} [Countable α] (x : α) : enc x ∈ Vt l := natZ_mem_Vt hl _

theorem tagZ_mem_Vt {n : ℕ} {x : V} (hx : x ∈ Vt l) : tagZ n x ∈ Vt l :=
  pair_mem_Vt (natZ_mem_Vt (le_of_mem_Vt hx) n) hx

theorem quad_mem_Vt {a b c d : V} (ha : a ∈ Vt l) (hb : b ∈ Vt l) (hc : c ∈ Vt l) (hd : d ∈ Vt l) :
    quad a b c d ∈ Vt l :=
  pair_mem_Vt ha (pair_mem_Vt hb (pair_mem_Vt hc hd))

theorem range_mem_Vt' {α : Type w} [Small.{5} α] (h : IsSmallAt l α) {f : α → V} (hf : ∀ a, f a ∈ Vt l)
    (hl : l ≤ 4) : ZFSet.range f ∈ Vt l :=
  range_mem_Vt l h f hf hl

theorem fnC_mem_Vt (hl : l ≤ 4) {α : Type} [Countable α] {F : α → V} (hF : ∀ x, F x ∈ Vt l) : fnC F ∈ Vt l :=
  range_mem_Vt' IsSmallAt.of_countable (fun x => pair_mem_Vt (enc_mem_Vt hl x) (hF x)) hl

instance (m : ℕ) : Countable (Dom m) := inferInstance

theorem mkKV_mem_Vt (hl : l ≤ 4) {F : (k : ℕ) → Hom k m → V} (hF : ∀ k f, F k f ∈ Vt l) : mkKV m F ∈ Vt l :=
  fnC_mem_Vt hl fun x => hF x.1 x.2

theorem apZ_mem_Vt (hl : l ≤ 4) {g : V} (hg : g ∈ Vt l) (x : V) : apZ g x ∈ Vt l := by
  by_cases h : ∃ y, pair x y ∈ g
  · exact Vt_of_below (below_apZ h) hg
  · rw [apZ, dif_neg h]; exact empty_mem_Vt hl

theorem π1_mem_Vt (hl : l ≤ 4) {z : V} (hz : z ∈ Vt l) : π1 z ∈ Vt l := by
  by_cases h : ∃ a b, z = pair a b
  · obtain ⟨a, b, rfl⟩ := h; rw [π1_pair]; exact Vt_of_below (below_pair_left _ _) hz
  · rw [π1, dif_neg h]; exact empty_mem_Vt hl

theorem π2_mem_Vt (hl : l ≤ 4) {z : V} (hz : z ∈ Vt l) : π2 z ∈ Vt l := by
  by_cases h : ∃ a b, z = pair a b
  · obtain ⟨a, b, rfl⟩ := h; rw [π2_pair]; exact Vt_of_below (below_pair_right _ _) hz
  · rw [π2, dif_neg h]; exact empty_mem_Vt hl

theorem dat_mem_Vt (hl : l ≤ 4) {v : V} (hv : v ∈ Vt l) (f : Hom k m) : dat v k f ∈ Vt l :=
  apZ_mem_Vt hl hv _

theorem here_mem_Vt (hl : l ≤ 4) {v : V} (hv : v ∈ Vt l) : here m v ∈ Vt l := dat_mem_Vt hl hv _

theorem res_mem_Vt' (hl : l ≤ 4) {v : V} (hv : v ∈ Vt l) (f : Hom k m) : res f v ∈ Vt l :=
  mkKV_mem_Vt hl fun _ _ => dat_mem_Vt hl hv _

theorem fnZ_mem_Vt {D : V} (hD : D ∈ Vt l) {F : V → V} (hF : ∀ x ∈ D, F x ∈ Vt l) : fnZ D F ∈ Vt l :=
  range_mem_Vt' (isSmallAt_of_mem_Vt hD) (fun x => pair_mem_Vt (Vt_trans l hD x.2) (hF x.1 x.2)) (le_of_mem_Vt hD)

theorem sep_mem_Vt {x : V} (hx : x ∈ Vt l) (p : V → Prop) : ZFSet.sep p x ∈ Vt l :=
  subset_mem_Vt hx fun z hz => (ZFSet.mem_sep.1 hz).1

theorem powerset_mem_Vt {x : V} (hx : x ∈ Vt l) : ZFSet.powerset x ∈ Vt l := by
  refine mem_Vt_of (le_of_mem_Vt hx) (fun y hy => subset_mem_Vt hx (ZFSet.mem_powerset.1 hy)) ?_
  refine (isSmallAt_of_mem_Vt hx).set.of_injective (f := fun y : ZFSet.powerset x => {z : x | z.1 ∈ y.1}) ?_
  intro a b h
  simp only at h
  apply Subtype.ext
  ext z
  constructor
  · intro hz
    have hzx : z ∈ x := ZFSet.mem_powerset.1 a.2 hz
    have : (⟨z, hzx⟩ : x) ∈ {z : x | z.1 ∈ a.1} := hz
    rw [h] at this; exact this
  · intro hz
    have hzx : z ∈ x := ZFSet.mem_powerset.1 b.2 hz
    have : (⟨z, hzx⟩ : x) ∈ {z : x | z.1 ∈ b.1} := hz
    rw [← h] at this; exact this

theorem prod_mem_Vt {x y : V} (hx : x ∈ Vt l) (hy : y ∈ Vt l) : ZFSet.prod x y ∈ Vt l := by
  have e : ZFSet.prod x y = ZFSet.range (fun p : x × y => pair p.1.1 p.2.1) := by
    ext z; simp only [ZFSet.mem_prod, ZFSet.mem_range]
    constructor
    · rintro ⟨a, ha, b, hb, rfl⟩; exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩
    · rintro ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, rfl⟩; exact ⟨a, ha, b, hb, rfl⟩
  rw [e]
  exact range_mem_Vt' ((isSmallAt_of_mem_Vt hx).prod (isSmallAt_of_mem_Vt hy))
    (fun p => pair_mem_Vt (Vt_trans l hx p.1.2) (Vt_trans l hy p.2.2)) (le_of_mem_Vt hx)

theorem funs_mem_Vt {x y : V} (hx : x ∈ Vt l) (hy : y ∈ Vt l) : ZFSet.funs x y ∈ Vt l :=
  sep_mem_Vt (powerset_mem_Vt (prod_mem_Vt hx hy)) _

theorem sUnion_mem_Vt {x : V} (hx : x ∈ Vt l) : ⋃₀ x ∈ Vt l := by
  refine mem_Vt_of (le_of_mem_Vt hx) (fun z hz => ?_) ?_
  · obtain ⟨y, hy, hz⟩ := ZFSet.mem_sUnion.1 hz
    exact Vt_trans l (Vt_trans l hx hy) hz
  · refine ((isSmallAt_of_mem_Vt hx).sigma (β := fun y : x => (y.1 : Type _))
      fun y => isSmallAt_of_mem_Vt (Vt_trans l hx y.2)).of_surjective
      (f := fun p => ⟨p.2.1, ZFSet.mem_sUnion.2 ⟨p.1.1, p.1.2, p.2.2⟩⟩) ?_
    rintro ⟨z, hz⟩
    obtain ⟨y, hy, hz⟩ := ZFSet.mem_sUnion.1 hz
    exact ⟨⟨⟨y, hy⟩, ⟨z, hz⟩⟩, rfl⟩

theorem iUnion_mem_Vt {α : Type w} [Small.{5} α] (h : IsSmallAt l α) {f : α → V} (hf : ∀ a, f a ∈ Vt l)
    (hl : l ≤ 4) : (⋃ a, f a : V) ∈ Vt l :=
  sUnion_mem_Vt (range_mem_Vt' h hf hl)

end

end Model
