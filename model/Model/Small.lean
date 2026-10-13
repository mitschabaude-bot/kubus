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

/-! ### Operations -/

section ops

variable (hl : l ≤ 4)
include hl

theorem El_mem_Vt {c : V} (hc : c ∈ Vt l) (f : Hom k m) : El c f ∈ Vt l :=
  π1_mem_Vt hl (π2_mem_Vt hl (dat_mem_Vt hl hc f))

theorem hcompAt_mem_Vt {c : V} (hc : c ∈ Vt l) (f : Hom k m) (φ : Cof k) (u : Tube k) (u0 : V) :
    hcompAt c f φ u u0 ∈ Vt l :=
  apZ_mem_Vt hl (π2_mem_Vt hl (π2_mem_Vt hl (π2_mem_Vt hl (dat_mem_Vt hl hc f)))) _

theorem transpAt_mem_Vt {c : V} (hc : c ∈ Vt l) (f : Hom (n + 1) m) (φ : Cof n) (a0 : V) :
    transpAt c f φ a0 ∈ Vt l :=
  apZ_mem_Vt hl (π1_mem_Vt hl (π2_mem_Vt hl (π2_mem_Vt hl (dat_mem_Vt hl hc f)))) _

theorem compF_mem_Vt {c : V} (hc : c ∈ Vt l) (f : Hom (k + 1) m) (φ : Cof k) (u : Tube k) (u0 : V) :
    compF c f φ u u0 ∈ Vt l := hcompAt_mem_Vt hl hc _ _ _ _

theorem appV_mem_Vt {v : V} (hv : v ∈ Vt l) (a : V) : appV k v a ∈ Vt l := apZ_mem_Vt hl (here_mem_Vt hl hv) a

theorem pappV_mem_Vt {v : V} (hv : v ∈ Vt l) (r : DM k) : pappV k v r ∈ Vt l := apZ_mem_Vt hl (here_mem_Vt hl hv) _

theorem fstV_mem_Vt {v : V} (hv : v ∈ Vt l) : fstV k v ∈ Vt l := π1_mem_Vt hl (here_mem_Vt hl hv)

theorem sndV_mem_Vt {v : V} (hv : v ∈ Vt l) : sndV k v ∈ Vt l := π2_mem_Vt hl (here_mem_Vt hl hv)

theorem pairV_mem_Vt {a b : V} (ha : a ∈ Vt l) (hb : b ∈ Vt l) : pairV k a b ∈ Vt l :=
  mkKV_mem_Vt hl fun _ g => pair_mem_Vt (res_mem_Vt' hl ha g) (res_mem_Vt' hl hb g)

theorem lamV_mem_Vt {D : (n : ℕ) → Hom n k → V} {F : (n : ℕ) → Hom n k → V → V} (hD : ∀ n g, D n g ∈ Vt l)
    (hF : ∀ n g, ∀ a ∈ D n g, F n g a ∈ Vt l) : lamV k D F ∈ Vt l :=
  mkKV_mem_Vt hl fun n g => fnZ_mem_Vt (hD n g) (hF n g)

theorem famV_mem_Vt {A : V} (hA : A ∈ Vt l) {F : (k : ℕ) → Hom k m → V → V}
    (hF : ∀ k f, ∀ a ∈ El A f, F k f a ∈ Vt l) : famV m A F ∈ Vt l :=
  lamV_mem_Vt hl (fun _ f => El_mem_Vt hl hA f) hF

theorem pathOfLine_mem_Vt {p : V} (hp : p ∈ Vt l) : pathOfLine k p ∈ Vt l :=
  mkKV_mem_Vt hl fun _ g => fnC_mem_Vt hl fun r => res_mem_Vt' hl hp _

theorem eqFun_mem_Vt {e : V} (he : e ∈ Vt l) (x : V) : eqFun n e x ∈ Vt l :=
  appV_mem_Vt hl (fstV_mem_Vt hl he) x

theorem ungAt_mem_Vt {e g : V} (he : e ∈ Vt l) (hg : g ∈ Vt l) (φ : Cof n) : ungAt n φ e g ∈ Vt l := by
  unfold ungAt
  split_ifs
  · exact eqFun_mem_Vt hl he g
  · exact empty_mem_Vt hl
  · exact π2_mem_Vt hl (π2_mem_Vt hl (here_mem_Vt hl hg))

theorem glueV_mem_Vt {tp a : V} (htp : tp ∈ Vt l) (ha : a ∈ Vt l) (φ : Cof k) : glueV k φ tp a ∈ Vt l := by
  refine mkKV_mem_Vt hl fun n g => ?_
  split_ifs
  · exact here_mem_Vt hl (dat_mem_Vt hl htp g)
  · exact tagZ_mem_Vt (pair_mem_Vt (res_mem_Vt' hl htp g) (res_mem_Vt' hl ha g))

theorem partialKV_mem_Vt {φ : Cof m} {F : (k : ℕ) → Hom k m → V} (hF : ∀ k f, (φ.restr f).holds → F k f ∈ Vt l) :
    partialKV m φ F ∈ Vt l := by
  refine mkKV_mem_Vt hl fun k f => ?_
  split_ifs with h
  · exact hF k f h
  · exact empty_mem_Vt hl

theorem tubeZ_mem_Vt {φ : Cof k} {u : Tube k} (hu : ∀ n h r, (φ.restr h).holds → u n h r ∈ Vt l) :
    tubeZ φ u ∈ Vt l := by
  refine fnC_mem_Vt hl fun x => ?_
  simp only [Tube.canon]
  split_ifs with h
  · exact hu _ _ _ h
  · exact empty_mem_Vt hl

theorem trGraph_mem_Vt {E0 : V} (hE0 : E0 ∈ Vt l) {F : Cof n → V → V} (hF : ∀ φ a, a ∈ E0 → F φ a ∈ Vt l) :
    trGraph n E0 F ∈ Vt l :=
  range_mem_Vt' (IsSmallAt.of_countable.prod (isSmallAt_of_mem_Vt hE0))
    (fun x => pair_mem_Vt (pair_mem_Vt (enc_mem_Vt hl _) (Vt_trans l hE0 x.2.2)) (hF _ _ x.2.2)) hl

instance (k : ℕ) : Countable (TubeDom k) := inferInstance

theorem hcGraph_mem_Vt {E : (n : ℕ) → Hom n k → V} (hE : ∀ n g, E n g ∈ Vt l) {F : Cof k → Tube k → V → V}
    (hF : ∀ φ u u0, (∀ n h r, u n h r ∈ Vt l) → u0 ∈ Vt l → F φ u u0 ∈ Vt l) : hcGraph k E F ∈ Vt l := by
  have hu : ∀ x : HcIn k E, ∀ n (h : Hom n k) r, x.tube n h r ∈ Vt l := fun x n h r =>
    Vt_trans l (insert_mem_Vt (empty_mem_Vt hl) (hE _ _)) (x.2.1 ⟨n, h, r⟩).2
  refine range_mem_Vt' ?_ (fun x => pair_mem_Vt (pair_mem_Vt (enc_mem_Vt hl _) (pair_mem_Vt
    (tubeZ_mem_Vt hl fun n h r _ => hu x n h r) (Vt_trans l (hE k (Hom.id k)) x.2.2.2)))
    (hF _ _ _ (fun n h r => ?_) (Vt_trans l (hE k (Hom.id k)) x.2.2.2))) hl
  · exact IsSmallAt.of_countable.sigma fun _ =>
      (IsSmallAt.pi IsSmallAt.of_countable fun (y : TubeDom k) =>
        isSmallAt_of_mem_Vt (insert_mem_Vt (empty_mem_Vt hl) (hE y.1 y.2.1))).prod
      (isSmallAt_of_mem_Vt (hE k (Hom.id k)))
  · simp only [Tube.canon]; split_ifs
    · exact hu x n h r
    · exact empty_mem_Vt hl

theorem piEl_mem_Vt {D : (n : ℕ) → Hom n k → V} {R : (n : ℕ) → Hom n k → V → V} (hD : ∀ n g, D n g ∈ Vt l)
    (hR : ∀ n g a, R n g a ∈ Vt l) : piEl k D R ∈ Vt l := by
  have hfs : ∀ x : Dom k, ZFSet.funs (D x.1 x.2) (⋃ a : ↥(D x.1 x.2), R x.1 x.2 a.1) ∈ Vt l := fun x =>
    funs_mem_Vt (hD _ _) (iUnion_mem_Vt (isSmallAt_of_mem_Vt (hD _ _)) (fun a => hR _ _ _) hl)
  refine sep_mem_Vt (range_mem_Vt' (IsSmallAt.pi IsSmallAt.of_countable fun x => isSmallAt_of_mem_Vt (hfs x))
    (fun G => mkKV_mem_Vt hl fun n g => Vt_trans l (hfs ⟨n, g⟩) (G ⟨n, g⟩).2) hl) _

end ops

/-! ### Codes -/

section codes

variable (hl : l ≤ 4)
include hl

theorem piElSet_mem_Vt {A B : V} (hA : A ∈ Vt l) (hB : B ∈ Vt l) : piElSet k A B ∈ Vt l :=
  piEl_mem_Vt hl (fun _ g => El_mem_Vt hl hA g)
    fun n g a => El_mem_Vt hl (apZ_mem_Vt hl (dat_mem_Vt hl hB g) a) _

theorem piC_mem_Vt' {A B : V} (hA : A ∈ Vt l) (hB : B ∈ Vt l) : piC m A B ∈ Vt l := by
  refine mkKV_mem_Vt hl fun k f => ?_
  have hA' := res_mem_Vt' hl hA f
  have hB' := res_mem_Vt' hl hB f
  refine quad_mem_Vt (tagZ_mem_Vt (pair_mem_Vt hA' hB')) (piElSet_mem_Vt hl hA' hB') ?_ ?_
  · rcases k with _ | n
    · exact empty_mem_Vt hl
    · exact trGraph_mem_Vt hl (piElSet_mem_Vt hl (res_mem_Vt' hl hA' _) (res_mem_Vt' hl hB' _)) fun φ a _ =>
        lamV_mem_Vt hl (fun _ g => El_mem_Vt hl hA' _) fun n' g v _ =>
          transpAt_mem_Vt hl (apZ_mem_Vt hl (dat_mem_Vt hl hB' _) _) _ _ _
  · exact hcGraph_mem_Vt hl (fun n g => piElSet_mem_Vt hl (res_mem_Vt' hl hA' g) (res_mem_Vt' hl hB' g))
      fun φ u u0 _ _ => lamV_mem_Vt hl (fun _ g => El_mem_Vt hl hA' g) fun n g v _ =>
        hcompAt_mem_Vt hl (apZ_mem_Vt hl (dat_mem_Vt hl hB' g) v) _ _ _ _

theorem sigmaElSet_mem_Vt {A B : V} (hA : A ∈ Vt l) (hB : B ∈ Vt l) : sigmaElSet k A B ∈ Vt l := by
  have hD := El_mem_Vt hl hA (Hom.id k)
  have hR : ∀ a, El (apZ (dat B k (Hom.id k)) a) (Hom.id k) ∈ Vt l := fun a =>
    El_mem_Vt hl (apZ_mem_Vt hl (dat_mem_Vt hl hB _) a) _
  exact range_mem_Vt' ((isSmallAt_of_mem_Vt hD).sigma fun a => isSmallAt_of_mem_Vt (hR a.1))
    (fun x => pairV_mem_Vt hl (Vt_trans l hD x.1.2) (Vt_trans l (hR _) x.2.2)) hl

theorem sigmaC_mem_Vt' {A B : V} (hA : A ∈ Vt l) (hB : B ∈ Vt l) : sigmaC m A B ∈ Vt l := by
  refine mkKV_mem_Vt hl fun k f => ?_
  have hA' := res_mem_Vt' hl hA f
  have hB' := res_mem_Vt' hl hB f
  refine quad_mem_Vt (tagZ_mem_Vt (pair_mem_Vt hA' hB')) (sigmaElSet_mem_Vt hl hA' hB') ?_ ?_
  · rcases k with _ | n
    · exact empty_mem_Vt hl
    · exact trGraph_mem_Vt hl (sigmaElSet_mem_Vt hl (res_mem_Vt' hl hA' _) (res_mem_Vt' hl hB' _)) fun φ a _ =>
        pairV_mem_Vt hl (transpAt_mem_Vt hl hA' _ _ _)
          (transpAt_mem_Vt hl (apZ_mem_Vt hl (dat_mem_Vt hl hB' _) _) _ _ _)
  · exact hcGraph_mem_Vt hl (fun n g => sigmaElSet_mem_Vt hl (res_mem_Vt' hl hA' g) (res_mem_Vt' hl hB' g))
      fun φ u u0 _ _ => pairV_mem_Vt hl (hcompAt_mem_Vt hl hA' _ _ _ _)
        (compF_mem_Vt hl (apZ_mem_Vt hl (dat_mem_Vt hl hB' _) _) _ _ _ _)

theorem pathElSet_mem_Vt {L a0 a1 : V} (hL : L ∈ Vt l) : pathElSet k L a0 a1 ∈ Vt l := by
  have hE := El_mem_Vt hl hL (Hom.id (k + 1))
  unfold pathElSet pathEl
  exact sep_mem_Vt (range_mem_Vt' (isSmallAt_of_mem_Vt hE)
    (fun p => pathOfLine_mem_Vt hl (Vt_trans l hE p.2)) hl) _

theorem pathC_mem_Vt' {L a0 a1 : V} (hL : L ∈ Vt l) (ha0 : a0 ∈ Vt l) (ha1 : a1 ∈ Vt l) :
    pathC m L a0 a1 ∈ Vt l := by
  refine mkKV_mem_Vt hl fun k f => ?_
  have hL' := res_mem_Vt' hl hL (Hom.lift f)
  have h0 := res_mem_Vt' hl ha0 f
  have h1 := res_mem_Vt' hl ha1 f
  refine quad_mem_Vt (tagZ_mem_Vt (pair_mem_Vt hL' (pair_mem_Vt h0 h1))) (pathElSet_mem_Vt hl hL') ?_ ?_
  · rcases k with _ | n
    · exact empty_mem_Vt hl
    · exact trGraph_mem_Vt hl (pathElSet_mem_Vt hl (res_mem_Vt' hl hL' _)) fun φ a _ =>
        pathOfLine_mem_Vt hl (compF_mem_Vt hl hL' _ _ _ _)
  · exact hcGraph_mem_Vt hl (fun n g => pathElSet_mem_Vt hl (res_mem_Vt' hl hL' _))
      fun φ u u0 _ _ => pathOfLine_mem_Vt hl (hcompAt_mem_Vt hl hL' _ _ _ _)

theorem ipiElSet_mem_Vt {L : V} (hL : L ∈ Vt l) : ipiElSet k L ∈ Vt l := by
  have hE := El_mem_Vt hl hL (Hom.id (k + 1))
  exact range_mem_Vt' (isSmallAt_of_mem_Vt hE) (fun p => pathOfLine_mem_Vt hl (Vt_trans l hE p.2)) hl

theorem ipiC_mem_Vt' {L : V} (hL : L ∈ Vt l) : ipiC m L ∈ Vt l := by
  refine mkKV_mem_Vt hl fun k f => ?_
  have hL' := res_mem_Vt' hl hL (Hom.lift f)
  refine quad_mem_Vt (tagZ_mem_Vt (pair_mem_Vt hL' (empty_mem_Vt hl))) (ipiElSet_mem_Vt hl hL') ?_ ?_
  · rcases k with _ | n
    · exact empty_mem_Vt hl
    · exact trGraph_mem_Vt hl (ipiElSet_mem_Vt hl (res_mem_Vt' hl hL' _)) fun φ a _ =>
        pathOfLine_mem_Vt hl (transpAt_mem_Vt hl hL' _ _ _)
  · exact hcGraph_mem_Vt hl (fun n g => ipiElSet_mem_Vt hl (res_mem_Vt' hl hL' _))
      fun φ u u0 _ _ => pathOfLine_mem_Vt hl (hcompAt_mem_Vt hl hL' _ _ _ _)

theorem fiberM_mem_Vt {T A f y : V} (hT : T ∈ Vt l) (hA : A ∈ Vt l) (hf : f ∈ Vt l) (hy : y ∈ Vt l) :
    fiberM k T A f y ∈ Vt l :=
  sigmaC_mem_Vt' hl hT (famV_mem_Vt hl hT fun k' g t ht =>
    pathC_mem_Vt' hl (res_mem_Vt' hl (res_mem_Vt' hl hA g) _) (appV_mem_Vt hl (res_mem_Vt' hl hf g) t)
      (res_mem_Vt' hl hy g))

theorem gtResult_mem_Vt {A : V} {φ : Cof (n + 1)} {Tp ep : V} (hA : A ∈ Vt l) (hTp : Tp ∈ Vt l) (hep : ep ∈ Vt l)
    (ψ : Cof n) (u0 : V) : gtResult A φ Tp ep ψ u0 ∈ Vt l := by
  have hext : ∀ k (g : Hom k n), gtExt A φ Tp ep ψ u0 g ∈ Vt l := fun k g =>
    hcompAt_mem_Vt hl (fiberM_mem_Vt hl (dat_mem_Vt hl hTp _) (res_mem_Vt' hl hA _)
      (fstV_mem_Vt hl (dat_mem_Vt hl hep _)) (res_mem_Vt' hl (compF_mem_Vt hl hA _ _ _ _) g)) _ _ _ _
  unfold gtResult
  split_ifs
  · exact fstV_mem_Vt hl (hext _ _)
  · exact glueV_mem_Vt hl (partialKV_mem_Vt hl fun k g _ => fstV_mem_Vt hl (hext k g))
      (hcompAt_mem_Vt hl hA _ _ _ _) _

theorem glueElSet_mem_Vt {A : V} {φ : Cof k} {Tp ep : V} (hA : A ∈ Vt l) (hTp : Tp ∈ Vt l) :
    glueElSet k A φ Tp ep ∈ Vt l := by
  have hE : ∀ y : Dom k, (insert ∅ (El (dat Tp y.1 y.2) (Hom.id y.1)) : V) ∈ Vt l := fun y =>
    insert_mem_Vt (empty_mem_Vt hl) (El_mem_Vt hl (dat_mem_Vt hl hTp _) _)
  have hEA := El_mem_Vt hl hA (Hom.id k)
  refine sep_mem_Vt (range_mem_Vt' ((IsSmallAt.pi IsSmallAt.of_countable fun y => isSmallAt_of_mem_Vt (hE y)).prod
    (isSmallAt_of_mem_Vt hEA)) (fun x => glueV_mem_Vt hl (partialKV_mem_Vt hl fun n g _ =>
      Vt_trans l (hE ⟨n, g⟩) (x.1 ⟨n, g⟩).2) (Vt_trans l hEA x.2.2) _) hl) _

theorem glueC_mem_Vt' {A : V} {φ : Cof m} {Tp ep : V} (hA : A ∈ Vt l) (hTp : Tp ∈ Vt l) (hep : ep ∈ Vt l) :
    glueC m A φ Tp ep ∈ Vt l := by
  refine mkKV_mem_Vt hl fun k f => ?_
  split_ifs
  · exact here_mem_Vt hl (dat_mem_Vt hl hTp f)
  have hA' := res_mem_Vt' hl hA f
  have hT' := res_mem_Vt' hl hTp f
  have he' := res_mem_Vt' hl hep f
  refine quad_mem_Vt (tagZ_mem_Vt (pair_mem_Vt hA' (pair_mem_Vt (enc_mem_Vt hl _) (pair_mem_Vt hT' he'))))
    (glueElSet_mem_Vt hl hA' hT') ?_ ?_
  · rcases k with _ | n
    · exact empty_mem_Vt hl
    · refine trGraph_mem_Vt hl ?_ fun ψ a _ => gtResult_mem_Vt hl hA' hT' he' ψ a
      split_ifs
      · exact El_mem_Vt hl (dat_mem_Vt hl hT' _) _
      · exact glueElSet_mem_Vt hl (res_mem_Vt' hl hA' _) (res_mem_Vt' hl hT' _)
  · refine hcGraph_mem_Vt hl (fun n g => ?_) fun ψ u u0 _ _ => ?_
    · split_ifs
      · exact El_mem_Vt hl (dat_mem_Vt hl hT' _) _
      · exact glueElSet_mem_Vt hl (res_mem_Vt' hl hA' _) (res_mem_Vt' hl hT' _)
    · exact glueV_mem_Vt hl (partialKV_mem_Vt hl fun n g _ => hcompAt_mem_Vt hl (dat_mem_Vt hl hT' _) _ _ _ _)
        (hcompAt_mem_Vt hl hA' _ _ _ _) _

theorem emptyC_mem_Vt' : emptyC m ∈ Vt l :=
  mkKV_mem_Vt hl fun _ _ => quad_mem_Vt (tagZ_mem_Vt (empty_mem_Vt hl)) (empty_mem_Vt hl) (empty_mem_Vt hl)
    (empty_mem_Vt hl)

end codes

theorem isContrM_mem_Vt {X : V} (hX : X ∈ Vt l) : isContrM k X ∈ Vt l := by
  have hl := le_of_mem_Vt hX
  exact sigmaC_mem_Vt' hl hX (famV_mem_Vt hl hX fun k' g c hc => piC_mem_Vt' hl (res_mem_Vt' hl hX g)
    (famV_mem_Vt hl (res_mem_Vt' hl hX g) fun k'' h x hx => pathC_mem_Vt' hl
      (res_mem_Vt' hl (res_mem_Vt' hl (res_mem_Vt' hl hX g) h) _)
      (res_mem_Vt' hl (Vt_trans l (El_mem_Vt hl hX g) hc) h)
      (Vt_trans l (El_mem_Vt hl (res_mem_Vt' hl hX g) h) hx)))

theorem isEquivM_mem_Vt {T A f : V} (hT : T ∈ Vt l) (hA : A ∈ Vt l) (hf : f ∈ Vt l) : isEquivM k T A f ∈ Vt l := by
  have hl := le_of_mem_Vt hT
  exact piC_mem_Vt' hl hA (famV_mem_Vt hl hA fun k' g y hy => isContrM_mem_Vt (fiberM_mem_Vt hl
    (res_mem_Vt' hl hT g) (res_mem_Vt' hl hA g) (res_mem_Vt' hl hf g) (Vt_trans l (El_mem_Vt hl hA g) hy)))

theorem eqFunL_mem_Vt {B : V} (hB : B ∈ Vt l) : eqFunL n B ∈ Vt l := by
  have hl := le_of_mem_Vt hB
  exact lamV_mem_Vt hl (fun _ g => El_mem_Vt hl (res_mem_Vt' hl (res_mem_Vt' hl hB _) _) g)
    fun _ g x _ => transpAt_mem_Vt hl hB _ _ _

theorem idEqV_mem_Vt {T F : V} (hT : T ∈ Vt l) (hF : F ∈ Vt l) : idEqV n T F ∈ Vt l := by
  have hl := le_of_mem_Vt hT
  refine lamV_mem_Vt hl (fun _ g => El_mem_Vt hl hT g) fun k g y hy => ?_
  have hy' := Vt_trans l (El_mem_Vt hl hT g) hy
  refine pairV_mem_Vt hl (pairV_mem_Vt hl hy' (pathOfLine_mem_Vt hl (res_mem_Vt' hl hy' _))) ?_
  have hX := fiberM_mem_Vt hl (res_mem_Vt' hl hT g) (res_mem_Vt' hl hT g) (res_mem_Vt' hl hF g) hy' (k := k)
  refine lamV_mem_Vt hl (fun _ g' => El_mem_Vt hl hX g') fun k' _ z hz => ?_
  have hz' := Vt_trans l (El_mem_Vt hl hX _) hz
  exact pathOfLine_mem_Vt hl (pairV_mem_Vt hl (pappV_mem_Vt hl (res_mem_Vt' hl (sndV_mem_Vt hl hz') _) _)
    (pathOfLine_mem_Vt hl (res_mem_Vt' hl (pappV_mem_Vt hl (res_mem_Vt' hl (sndV_mem_Vt hl hz') _) _) _)))

theorem eqTr_mem_Vt {B : V} (hB : B ∈ Vt l) : eqTr n B ∈ Vt l := by
  have hl := le_of_mem_Vt hB
  exact pairV_mem_Vt hl (res_mem_Vt' hl (eqFunL_mem_Vt hB) _) (transpAt_mem_Vt hl
    (isEquivM_mem_Vt (res_mem_Vt' hl (res_mem_Vt' hl hB _) _) hB (eqFunL_mem_Vt hB)) _ _ _)

theorem univHcF_mem_Vt (hl : l ≤ 4) {φ : Cof k} {u : Tube k} {u0 : V} (hu : ∀ n h r, u n h r ∈ Vt l)
    (hu0 : u0 ∈ Vt l) : univHcF k φ u u0 ∈ Vt l := by
  unfold univHcF
  split_ifs
  · exact hu _ _ _
  · exact glueC_mem_Vt' hl hu0 (partialKV_mem_Vt hl fun n g _ => hu _ _ _)
      (partialKV_mem_Vt hl fun n g _ => eqTr_mem_Vt (res_mem_Vt' hl (hu _ _ _) _))

theorem univC_mem_Vt' {l : ℕ} (hl : l < 4) : univC m l ∈ Vt (l + 1) := by
  have hl' : l + 1 ≤ 4 := hl
  have hV := Vt_mem_succ l hl
  unfold univC univCode univDatum
  refine mkKV_mem_Vt hl' fun k f => ?_
  refine quad_mem_Vt (tagZ_mem_Vt (natZ_mem_Vt hl' _)) (sep_mem_Vt hV _) ?_
    (hcGraph_mem_Vt hl' (fun n _ => sep_mem_Vt hV _) fun φ u u0 hu hu0 => univHcF_mem_Vt hl' hu hu0)
  rcases k with _ | n
  · exact empty_mem_Vt hl'
  · unfold univTr
    exact trGraph_mem_Vt hl' (sep_mem_Vt hV _) fun φ a ha => Vt_trans _ (sep_mem_Vt hV _) ha

/-! ### Interpretations -/

theorem TEnv.cons_mem_Vt {γ : ℕ → V} (hγ : ∀ x, γ x ∈ Vt l) {a : V} (ha : a ∈ Vt l) :
    ∀ x, TEnv.cons γ a x ∈ Vt l
  | 0 => ha
  | x + 1 => hγ x

/-- All values of the signature semantics are small. -/
def SigV.Small (l : ℕ) (σ : SigV) : Prop :=
  (∀ m c, σ.cst m c ∈ Vt l) ∧ (∀ m d ps, σ.dat m d ps ∈ Vt l) ∧
  (∀ m d c ps args rs, σ.con m d c ps args rs ∈ Vt l) ∧ (∀ m d ps P bs t, σ.elim m d ps P bs t ∈ Vt l)

theorem SigV.small_empty (hl : l ≤ 4) : SigV.Small l SigV.empty :=
  ⟨fun _ _ => empty_mem_Vt hl, fun _ _ _ => empty_mem_Vt hl, fun _ _ _ _ _ _ => empty_mem_Vt hl,
    fun _ _ _ _ _ _ => empty_mem_Vt hl⟩

theorem interp_mem_Vt (hl : l ≤ 4) {cst : SigV} {uc : ℕ → ℕ → V} {good : (m : ℕ) → V → Prop}
    (hcst : SigV.Small l cst) (huc : ∀ m l', uc m l' ∈ Vt l) :
    ∀ (t : KubusCore.Tm) (m : ℕ) (ρ : IEnv m) (γ : ℕ → V), (∀ x, γ x ∈ Vt l) →
      interp cst uc good t m ρ γ ∈ Vt l := by
  have hr : ∀ {m k : ℕ} {γ : ℕ → V}, (∀ x, γ x ∈ Vt l) → ∀ (f : Hom k m), ∀ x, TEnv.restr γ f x ∈ Vt l :=
    fun hγ f x => res_mem_Vt' hl (hγ x) f
  intro t
  induction t with
  | var x => intro m ρ γ hγ; exact hγ x
  | const c => intro m ρ γ hγ; exact hcst.1 m c
  | tnil => intro m ρ γ hγ; exact empty_mem_Vt hl
  | tcons t ts iht ihts => intro m ρ γ hγ; exact pair_mem_Vt (iht m ρ γ hγ) (ihts m ρ γ hγ)
  | data d ps _ => intro m ρ γ hγ; exact hcst.2.1 _ _ _
  | con d c ps args rs _ _ => intro m ρ γ hγ; exact hcst.2.2.1 _ _ _ _ _ _
  | elim d ps P bs t _ _ _ _ => intro m ρ γ hγ; exact hcst.2.2.2 _ _ _ _ _ _
  | univ l' => intro m ρ γ hγ; exact huc m l'
  | pi A B ihA ihB =>
    intro m ρ γ hγ; simp only [interp]; split_ifs
    · exact piC_mem_Vt' hl (ihA m ρ γ hγ) (famV_mem_Vt hl (ihA m ρ γ hγ) fun k f a ha =>
        ihB _ _ _ (TEnv.cons_mem_Vt (hr hγ f) (Vt_trans l (El_mem_Vt hl (ihA m ρ γ hγ) f) ha)))
    · exact empty_mem_Vt hl
  | sigma A B ihA ihB =>
    intro m ρ γ hγ; simp only [interp]; split_ifs
    · exact sigmaC_mem_Vt' hl (ihA m ρ γ hγ) (famV_mem_Vt hl (ihA m ρ γ hγ) fun k f a ha =>
        ihB _ _ _ (TEnv.cons_mem_Vt (hr hγ f) (Vt_trans l (El_mem_Vt hl (ihA m ρ γ hγ) f) ha)))
    · exact empty_mem_Vt hl
  | lam A t ihA iht =>
    intro m ρ γ hγ; simp only [interp]
    exact lamV_mem_Vt hl (fun _ f => El_mem_Vt hl (ihA m ρ γ hγ) f) fun k f a ha =>
      iht _ _ _ (TEnv.cons_mem_Vt (hr hγ f) (Vt_trans l (El_mem_Vt hl (ihA m ρ γ hγ) f) ha))
  | app f a ihf iha =>
    intro m ρ γ hγ; simp only [interp]; split_ifs
    · exact appV_mem_Vt hl (ihf m ρ γ hγ) _
    · exact empty_mem_Vt hl
  | pair a b iha ihb =>
    intro m ρ γ hγ; simp only [interp]; split_ifs
    · exact pairV_mem_Vt hl (iha m ρ γ hγ) (ihb m ρ γ hγ)
    · exact empty_mem_Vt hl
  | fst p ih => intro m ρ γ hγ; simp only [interp]; exact fstV_mem_Vt hl (ih m ρ γ hγ)
  | snd p ih => intro m ρ γ hγ; simp only [interp]; exact sndV_mem_Vt hl (ih m ρ γ hγ)
  | path A a b ihA iha ihb =>
    intro m ρ γ hγ; simp only [interp]; split_ifs
    · exact pathC_mem_Vt' hl (ihA _ _ _ (hr hγ _)) (iha m ρ γ hγ) (ihb m ρ γ hγ)
    · exact empty_mem_Vt hl
  | plam t ih =>
    intro m ρ γ hγ; simp only [interp]; split_ifs
    · exact pathOfLine_mem_Vt hl (ih _ _ _ (hr hγ _))
    · exact empty_mem_Vt hl
  | papp p r ih => intro m ρ γ hγ; simp only [interp]; exact pappV_mem_Vt hl (ih m ρ γ hγ) _
  | ipi A ih =>
    intro m ρ γ hγ; simp only [interp]; split_ifs
    · exact ipiC_mem_Vt' hl (ih _ _ _ (hr hγ _))
    · exact empty_mem_Vt hl
  | split φ t ψ u iht ihu =>
    intro m ρ γ hγ; simp only [interp]; split_ifs
    all_goals first | exact iht m ρ γ hγ | exact ihu m ρ γ hγ | exact empty_mem_Vt hl
  | abort => intro m ρ γ hγ; simp only [interp]; exact empty_mem_Vt hl
  | transp A φ a ihA iha =>
    intro m ρ γ hγ; simp only [interp]; split_ifs
    · exact transpAt_mem_Vt hl (ihA _ _ _ (hr hγ _)) _ _ _
    · exact empty_mem_Vt hl
  | hcomp A φ u a ihA ihu iha =>
    intro m ρ γ hγ; simp only [interp]; split_ifs
    · exact hcompAt_mem_Vt hl (ihA m ρ γ hγ) _ _ _ _
    · exact empty_mem_Vt hl
  | glue A φ T e ihA ihT ihe =>
    intro m ρ γ hγ; simp only [interp]; split_ifs
    · exact glueC_mem_Vt' hl (ihA m ρ γ hγ) (partialKV_mem_Vt hl fun k f _ => ihT _ _ _ (hr hγ f))
        (partialKV_mem_Vt hl fun k f _ => ihe _ _ _ (hr hγ f))
    · exact empty_mem_Vt hl
  | glueEl φ e t a ihe iht iha =>
    intro m ρ γ hγ; simp only [interp]; split_ifs
    · exact iht m ρ γ hγ
    · exact empty_mem_Vt hl
    · exact glueV_mem_Vt hl (partialKV_mem_Vt hl fun k f _ => iht _ _ _ (hr hγ f)) (iha m ρ γ hγ) _
    · exact empty_mem_Vt hl
  | unglue φ e g ihe ihg =>
    intro m ρ γ hγ; simp only [interp]; exact ungAt_mem_Vt hl (ihe m ρ γ hγ) (ihg m ρ γ hγ) _

theorem equivCode_mem_Vt' {T A : V} (hT : T ∈ Vt l) (hA : A ∈ Vt l) : equivCode m T A ∈ Vt l := by
  have hl := le_of_mem_Vt hT
  exact interp_mem_Vt hl (SigV.small_empty hl) (fun _ _ => empty_mem_Vt hl) _ _ _ _
    (TEnv.cons_mem_Vt (TEnv.cons_mem_Vt (fun _ => empty_mem_Vt hl) hT) hA)

end

end Model
