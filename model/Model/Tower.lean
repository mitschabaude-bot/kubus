import Model.Enc

/-!
# A finite tower of Grothendieck universes

`Vt l` (for `l ≤ 4`) is the embedded copy of `ZFSet.{l}` inside the value universe
`V = ZFSet.{5}` (Mathlib's `PSet.embed`). The key closure property is `range_mem_Vt`: the range
of an `l`-small family of members of `Vt l` is a member of `Vt l`.
-/

universe u v w

namespace PSet

theorem lift_equiv : ∀ {x y : PSet.{u}}, PSet.Equiv x y → PSet.Equiv (PSet.Lift.{u, v} x) (PSet.Lift.{u, v} y)
  | ⟨_, A⟩, ⟨_, B⟩, ⟨αβ, βα⟩ =>
    ⟨fun ⟨a⟩ => let ⟨b, h⟩ := αβ a; ⟨⟨b⟩, lift_equiv h⟩,
     fun ⟨b⟩ => let ⟨a, h⟩ := βα b; ⟨⟨a⟩, lift_equiv h⟩⟩

theorem mem_lift_iff {x : PSet.{u}} {y : PSet.{max u v}} :
    y ∈ PSet.Lift.{u, v} x ↔ ∃ i, PSet.Equiv y (PSet.Lift.{u, v} (x.Func i)) := by
  obtain ⟨α, A⟩ := x
  constructor
  · rintro ⟨⟨a⟩, h⟩; exact ⟨a, h⟩
  · rintro ⟨a, h⟩; exact ⟨⟨a⟩, h⟩

theorem mem_embed_iff {y : PSet.{max (u + 1) v}} :
    y ∈ embed.{u, v} ↔ ∃ x : PSet.{u}, PSet.Equiv y (PSet.Lift.{u, max (u + 1) v} x) := by
  constructor
  · rintro ⟨⟨x⟩, h⟩; exact ⟨x, h⟩
  · rintro ⟨x, h⟩; exact ⟨⟨x⟩, h⟩

end PSet

namespace Model

open ZFSet

/-- The embedded copy of `ZFSet.{u}`. -/
def embedSet : ZFSet.{max (u + 1) v} := ZFSet.mk PSet.embed.{u, v}

/-- Lift a `ZFSet.{u}`. -/
def liftZ : ZFSet.{u} → ZFSet.{max (u + 1) v} :=
  Quotient.map PSet.Lift.{u, max (u + 1) v} fun _ _ => PSet.lift_equiv

theorem liftZ_mk (x : PSet.{u}) : liftZ.{u, v} (ZFSet.mk x) = ZFSet.mk (PSet.Lift.{u, max (u + 1) v} x) := rfl

theorem mem_embedSet {y : ZFSet.{max (u + 1) v}} : y ∈ embedSet.{u, v} ↔ ∃ x : ZFSet.{u}, y = liftZ.{u, v} x := by
  induction y using Quotient.inductionOn with
  | h y =>
    show ZFSet.mk y ∈ ZFSet.mk _ ↔ _
    rw [ZFSet.mk_mem_iff, PSet.mem_embed_iff]
    constructor
    · rintro ⟨x, h⟩; exact ⟨ZFSet.mk x, ZFSet.sound h⟩
    · rintro ⟨x, h⟩
      induction x using Quotient.inductionOn with
      | h x => exact ⟨x, ZFSet.exact h⟩

theorem mem_liftZ {x : ZFSet.{u}} {y : ZFSet.{max (u + 1) v}} :
    y ∈ liftZ.{u, v} x ↔ ∃ z ∈ x, y = liftZ.{u, v} z := by
  induction x using Quotient.inductionOn with
  | h x =>
  induction y using Quotient.inductionOn with
  | h y =>
    show ZFSet.mk y ∈ ZFSet.mk _ ↔ _
    rw [ZFSet.mk_mem_iff, PSet.mem_lift_iff]
    constructor
    · rintro ⟨i, h⟩
      exact ⟨ZFSet.mk (x.Func i), ZFSet.mk_mem_iff.2 (PSet.func_mem x i), ZFSet.sound h⟩
    · rintro ⟨z, hz, h⟩
      induction z using Quotient.inductionOn with
      | h z =>
        obtain ⟨i, hi⟩ := ZFSet.mk_mem_iff.1 hz
        refine ⟨i, ?_⟩
        have := ZFSet.exact h
        exact this.trans (PSet.lift_equiv hi)

theorem embedSet_trans {y z : ZFSet.{max (u + 1) v}} (hy : y ∈ embedSet.{u, v}) (hz : z ∈ y) :
    z ∈ embedSet.{u, v} := by
  obtain ⟨x, rfl⟩ := mem_embedSet.1 hy
  obtain ⟨w, -, rfl⟩ := mem_liftZ.1 hz
  exact mem_embedSet.2 ⟨w, rfl⟩

end Model

namespace Model

open ZFSet

theorem range_mem_embedSet {α : Type w} [Small.{u} α] [Small.{max (u + 1) v} α]
    (f : α → ZFSet.{max (u + 1) v}) (hf : ∀ a, f a ∈ embedSet.{u, v}) :
    ZFSet.range f ∈ embedSet.{u, v} := by
  choose g hg using fun a => mem_embedSet.1 (hf a)
  refine mem_embedSet.2 ⟨ZFSet.range g, ?_⟩
  ext y
  rw [ZFSet.mem_range, mem_liftZ]
  constructor
  · rintro ⟨a, rfl⟩; exact ⟨g a, ZFSet.mem_range_self (f := g) a, hg a⟩
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨a, rfl⟩ := ZFSet.mem_range.1 hz
    exact ⟨a, hg a⟩

end Model

namespace PSet

theorem lift_lift : ∀ x : PSet.{u},
    PSet.Equiv (PSet.Lift.{max u v, w} (PSet.Lift.{u, v} x)) (PSet.Lift.{u, max v w} x)
  | ⟨_, A⟩ => ⟨fun ⟨⟨a⟩⟩ => ⟨⟨a⟩, lift_lift (A a)⟩, fun ⟨a⟩ => ⟨⟨⟨a⟩⟩, lift_lift (A a)⟩⟩

end PSet

namespace Model

open ZFSet

/-- `embedSet` at level `u` is a member of `embedSet` at level `u + 1`. -/
theorem embedSet_mem_succ : (embedSet.{u, max (u + 2) v} : ZFSet.{max (u + 2) v}) ∈ embedSet.{u + 1, v} := by
  rw [mem_embedSet]
  refine ⟨embedSet.{u, u + 1}, ?_⟩
  show ZFSet.mk _ = ZFSet.mk _
  apply ZFSet.sound
  refine ⟨fun ⟨x⟩ => ⟨⟨⟨x⟩⟩, (PSet.lift_lift.{u, u + 1, max (u + 2) v} x).symm⟩,
    fun ⟨⟨x⟩⟩ => ⟨⟨x⟩, (PSet.lift_lift.{u, u + 1, max (u + 2) v} x).symm⟩⟩

theorem embedSet_subset_succ {x : ZFSet.{max (u + 2) v}} (hx : x ∈ embedSet.{u, max (u + 2) v}) :
    x ∈ embedSet.{u + 1, v} := by
  obtain ⟨y, rfl⟩ := mem_embedSet.1 hx
  induction y using Quotient.inductionOn with
  | h y =>
    rw [mem_embedSet]
    refine ⟨liftZ.{u, u + 1} (ZFSet.mk y), ?_⟩
    show ZFSet.mk _ = ZFSet.mk _
    exact ZFSet.sound (PSet.lift_lift.{u, u + 1, max (u + 2) v} y).symm

end Model

/-! ### The concrete tower in `V = ZFSet.{5}` -/

namespace Model

/-- The Grothendieck universe for level `l ≤ 4` (empty above). -/
def Vt : ℕ → V
  | 0 => embedSet.{0, 5}
  | 1 => embedSet.{1, 5}
  | 2 => embedSet.{2, 5}
  | 3 => embedSet.{3, 5}
  | 4 => embedSet.{4, 5}
  | _ => ∅

theorem Vt_mem_succ : ∀ l, l < 4 → Vt l ∈ Vt (l + 1)
  | 0, _ => embedSet_mem_succ.{0, 5}
  | 1, _ => embedSet_mem_succ.{1, 5}
  | 2, _ => embedSet_mem_succ.{2, 5}
  | 3, _ => embedSet_mem_succ.{3, 5}
  | l + 4, h => absurd h (by omega)

theorem Vt_subset_succ : ∀ l, l < 4 → ∀ {x : V}, x ∈ Vt l → x ∈ Vt (l + 1)
  | 0, _, _, hx => embedSet_subset_succ.{0, 5} hx
  | 1, _, _, hx => embedSet_subset_succ.{1, 5} hx
  | 2, _, _, hx => embedSet_subset_succ.{2, 5} hx
  | 3, _, _, hx => embedSet_subset_succ.{3, 5} hx
  | l + 4, h, _, _ => absurd h (by omega)

theorem Vt_trans : ∀ l {x y : V}, x ∈ Vt l → y ∈ x → y ∈ Vt l
  | 0, _, _, hx, hy => embedSet_trans.{0, 5} hx hy
  | 1, _, _, hx, hy => embedSet_trans.{1, 5} hx hy
  | 2, _, _, hx, hy => embedSet_trans.{2, 5} hx hy
  | 3, _, _, hx, hy => embedSet_trans.{3, 5} hx hy
  | 4, _, _, hx, hy => embedSet_trans.{4, 5} hx hy
  | _ + 5, _, _, hx, _ => absurd hx (ZFSet.notMem_empty _)

/-- `α` is small for level `l`. -/
def IsSmallAt (l : ℕ) (α : Type w) : Prop :=
  match l with
  | 0 => Small.{0} α
  | 1 => Small.{1} α
  | 2 => Small.{2} α
  | 3 => Small.{3} α
  | 4 => Small.{4} α
  | _ => True

theorem range_mem_Vt : ∀ (l : ℕ) {α : Type w} [Small.{5} α] (_ : IsSmallAt l α) (f : α → V), (∀ a, f a ∈ Vt l) →
    l ≤ 4 → ZFSet.range f ∈ Vt l
  | 0, α, _, h, f, hf, _ => @range_mem_embedSet.{0, 5, w} α h _ f hf
  | 1, α, _, h, f, hf, _ => @range_mem_embedSet.{1, 5, w} α h _ f hf
  | 2, α, _, h, f, hf, _ => @range_mem_embedSet.{2, 5, w} α h _ f hf
  | 3, α, _, h, f, hf, _ => @range_mem_embedSet.{3, 5, w} α h _ f hf
  | 4, α, _, h, f, hf, _ => @range_mem_embedSet.{4, 5, w} α h _ f hf
  | _ + 5, _, _, _, _, _, hl => absurd hl (by omega)

end Model
