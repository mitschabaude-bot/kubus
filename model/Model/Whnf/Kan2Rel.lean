import Model.Whnf.Kan2Path
import Model.Whnf.Kan2PathT

/-!
# Kan properties of all types related to restrictions of a type

`KHRel S k Y`: compositions at every pair of types related to each other and to a restriction of `Y`;
`KTRel S k Y`: transports along every pair of such lines. Both pass from the line of a path type to the
path type (`khRel_path`, `ktRel_path`).
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

variable {S : Sig} {k : ℕ}

/-- Compositions at all pairs of types related to restrictions of `Y`. -/
def KHRel (S : Sig) (k : ℕ) (Y : Tm) : Prop :=
  ∀ k' (σ : ISub k' k) (X X' : Tm), RT2 S k' (Y.isub σ) X → RT2 S k' X X' → KanH2 S k' X X'

/-- Transports along all pairs of lines related to restrictions of `Y` to lines. -/
def KTRel (S : Sig) (k : ℕ) (Y : Tm) : Prop :=
  ∀ k' (Θ : ISub (k' + 1) k) (X X' : Tm), RT2 S (k' + 1) (Y.isub Θ) X → RT2 S (k' + 1) X X' → KanT2 S k' X X'

theorem KHRel.isub {Y : Tm} {k' : ℕ} (h : KHRel S k Y) (ρ : ISub k' k) : KHRel S k' (Y.isub ρ) :=
  fun k2 σ X X' h1 h2 => h k2 (ρ.comp σ) X X' (by rw [← Tm.isub_isub]; exact h1) h2

theorem KTRel.isub {Y : Tm} {k' : ℕ} (h : KTRel S k Y) (ρ : ISub k' k) : KTRel S k' (Y.isub ρ) :=
  fun k2 Θ X X' h1 h2 => h k2 (ρ.comp Θ) X X' (by rw [← Tm.isub_isub]; exact h1) h2

theorem KHRel.dshift {Y : Tm} (h : KHRel S k Y) : KHRel S (k + 1) Y.dshift :=
  fun k2 σ X X' h1 h2 => h k2 σ.tail X X' (by rw [← dshift_isub_tail]; exact h1) h2

theorem KTRel.dshift {Y : Tm} (h : KTRel S k Y) : KTRel S (k + 1) Y.dshift :=
  fun k2 Θ X X' h1 h2 => h k2 Θ.tail X X' (by rw [← dshift_isub_tail]; exact h1) h2

/-- A related type in the left form. -/
theorem KHRel.self {Y : Tm} (h : KHRel S k Y) {k' : ℕ} (σ : ISub k' k) (hYY : RT2 S k' (Y.isub σ) (Y.isub σ))
    {X' : Tm} (hX : RT2 S k' (Y.isub σ) X') : KanH2 S k' (Y.isub σ) X' :=
  h k' σ _ X' hYY hX

theorem KTRel.self {Y : Tm} (h : KTRel S k Y) {k' : ℕ} (Θ : ISub (k' + 1) k) (hYY : RT2 S (k' + 1) (Y.isub Θ) (Y.isub Θ))
    {X' : Tm} (hX : RT2 S (k' + 1) (Y.isub Θ) X') : KanT2 S k' (Y.isub Θ) X' :=
  h k' Θ _ X' hYY hX

variable (hW : WfSig S)
include hW

/-- The points of the lines of the normal forms of types related to restrictions of a path type are
related to restrictions of its line. -/
theorem pathRel_pt {L a b : Tm} {l : ℕ} (hp : HasTy S k .one [] (.path L a b) (.univ l)) {k' : ℕ} (σ : ISub k' k)
    {X : Tm} (hPX : RT2 S k' ((Tm.path L a b).isub σ) X) {k1 : ℕ} (ρ : ISub k1 k') {L2 c0 c1 : Tm}
    (hR : RedT S k1 (X.isub ρ) (.path L2 c0 c1)) (s : I) (hs : s.Scoped k1) {k2 : ℕ} (ρ' : ISub k2 k1) :
    RT2 S k2 (L.isub ((ISub.cons s hs (σ.comp ρ)).comp ρ')) ((L2.dinst s).isub ρ') := by
  have hpσ := HasTy.isubS hW hp σ
  rw [isub_path] at hpσ hPX
  have PS := PathStr_of hW hPX ⟨redW_self rfl, TyEq.refl _⟩ hpσ
  obtain ⟨L1, b0, b1, L1', b0', b1', h1, h1', hrel, -, -⟩ := PS.whnf k1 ρ
  rw [isub_path] at h1
  obtain ⟨rfl, -, -⟩ : (L.isub σ.up).isub ρ.up = L1 ∧ (a.isub σ).isub ρ = b0 ∧ (b.isub σ).isub ρ = b1 := by
    have := RedW.unique (redW_self rfl) h1.1; injection this; exact ⟨by assumption, by assumption, by assumption⟩
  obtain ⟨rfl, -, -⟩ : L1' = L2 ∧ b0' = c0 ∧ b1' = c1 := by
    have := RedW.unique h1'.1 hR.1; injection this; exact ⟨by assumption, by assumption, by assumption⟩
  have hc := PS.tc k1 ρ _ _ _ (by rw [isub_path]; exact h1) s hs
  have x := RT2.isub hW hc (hrel s s hs hs (I_eq_refl _)) ρ'
  rwa [Tm.isub_isub, ← ISub.up_comp, isub_up_dinst _ _ _ hs, Tm.isub_isub] at x

/-- The normal form of a type related to a restriction of a path type. -/
theorem pathRel_whnf {L a b : Tm} {l : ℕ} (hp : HasTy S k .one [] (.path L a b) (.univ l)) {k' : ℕ} (σ : ISub k' k)
    {X : Tm} (hPX : RT2 S k' ((Tm.path L a b).isub σ) X) :
    ∃ L2 c0 c1 l2, RedT S k' X (.path L2 c0 c1) ∧ HasTy S k' .one [] (.path L2 c0 c1) (.univ l2) := by
  have hpσ := HasTy.isubS hW hp σ
  rw [isub_path] at hpσ hPX
  have PS := PathStr_of hW hPX ⟨redW_self rfl, TyEq.refl _⟩ hpσ
  obtain ⟨-, -, -, L1', b0', b1', -, h1', -⟩ := PS.whnf k' (ISub.id k')
  have hXK := (Comp2_ty_base hPX).2.2.1
  rw [isub_id_of_closed (closed_of_isTyK hW hXK)] at h1'
  obtain ⟨l2, hp2⟩ := pathW_typed hW hXK h1'
  exact ⟨L1', b0', b1', l2, h1', hp2⟩

/-- Compositions at types related to path types whose lines have compositions. -/
theorem khRel_path {L a b : Tm} {l : ℕ} (hp : HasTy S k .one [] (.path L a b) (.univ l)) (hL : KHRel S (k + 1) L) :
    KHRel S k (.path L a b) := by
  intro k' σ X X' hPX hXX'
  obtain ⟨L2, c0, c1, l2, hR, hp2⟩ := pathRel_whnf hW hp σ hPX
  refine kanH2_path hW hXX' hR hp2 fun k1 ρ L3 d0 d1 hR3 s hs k2 ρ' X'' h => ?_
  exact hL k2 _ _ X'' (pathRel_pt hW hp σ hPX ρ hR3 s hs ρ') h

/-- Transports along lines of types related to path types whose lines have compositions and transports. -/
theorem ktRel_path {L a b : Tm} {l : ℕ} (hp : HasTy S k .one [] (.path L a b) (.univ l)) (hLH : KHRel S (k + 1) L)
    (hLT : KTRel S (k + 1) L) : KTRel S k (.path L a b) := by
  intro k' Θ X X' hPX hXX'
  obtain ⟨L2, c0, c1, l2, hR, hp2⟩ := pathRel_whnf hW hp Θ hPX
  refine kanT2_path hW hXX' hR hp2 (fun k1 ρ L3 d0 d1 hR3 s hs k2 ρ' X'' h => ?_)
    (fun k1 ρ L3 d0 d1 hR3 s hs k2 ρ' X'' h => ?_)
  · exact hLT k2 _ _ X'' (pathRel_pt hW hp Θ hPX ρ hR3 s hs ρ') h
  · exact hLH k2 _ _ X'' (pathRel_pt hW hp Θ hPX ρ hR3 s hs ρ') h

/-- The same for path types with constant lines. -/
theorem khRel_pathC {Y a b : Tm} {l : ℕ} (hp : HasTy S k .one [] (.pathC Y a b) (.univ l)) (hY : KHRel S k Y) :
    KHRel S k (.pathC Y a b) :=
  khRel_path hW hp hY.dshift

theorem ktRel_pathC {Y a b : Tm} {l : ℕ} (hp : HasTy S k .one [] (.pathC Y a b) (.univ l)) (hYH : KHRel S k Y)
    (hYT : KTRel S k Y) : KTRel S k (.pathC Y a b) :=
  ktRel_path hW hp hYH.dshift hYT.dshift

end Model.Whnf
