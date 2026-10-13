import Model.DataTot

/-!
# Inductive types: lines constant on a face

If the line of codes `dataC Θ` along `f` is constant on `φ`, then so are its element sets and its
argument types (at valid earlier arguments): the code records the argument types (`shapeV`).
-/

set_option autoImplicit false

namespace Model

open ZFSet KubusCore

noncomputable section

attribute [local instance] Classical.propDecidable

variable {k m n : ℕ}

theorem SData.restr_id (Θ : SData m) : Θ.restr (Hom.id m) = Θ := by
  cases Θ; simp only [SData.restr, Hom.id_comp]

theorem here_dataC (Θ : SData m) : here m (dataC Θ) = dataDatum Θ := by
  rw [dataC, here_mkKV, SData.restr_id]

/-- Valid earlier arguments: point arguments typed, recursive ones elements. -/
def SData.FullValid (Θ : SData m) (c n : ℕ) (g : Hom n m) (pre : List V) : Prop :=
  Θ.PtValid c n g pre ∧ ∀ i (hi : i < pre.length), (Θ.ctors.getD c default).isRec i = true → DElem Θ n g pre[i]

theorem shapeV_ty {Λ1 Λ2 : SData n} (hct : Λ1.ctors = Λ2.ctors) (hs : shapeV Λ1 = shapeV Λ2) {c : ℕ}
    (hc : c < Λ2.ctors.length) {j : ℕ} (hj : j ≤ (Λ2.ctors[c]).args.length)
    (p : VPref Λ2 (delemSet Λ2) n (Hom.id n) c Λ2.ctors[c] j) :
    Λ1.ty c j n (Hom.id n) p.1 = Λ2.ty c j n (Hom.id n) p.1 := by
  have hmem : ZFSet.pair (natZ c) (ZFSet.pair (natZ j) (ZFSet.pair (vlist p.1) (Λ2.ty c j n (Hom.id n) p.1)))
      ∈ shapeV Λ2 := by
    simp only [shapeV, ZFSet.mem_iUnion, ZFSet.mem_range]
    exact ⟨⟨c, hc⟩, ⟨j, Nat.lt_succ_of_le hj⟩, p, rfl⟩
  rw [← hs] at hmem
  simp only [shapeV, ZFSet.mem_iUnion, ZFSet.mem_range, pair_inj', natZ_inj] at hmem
  obtain ⟨c', j', p', h1, h2, h3, h4⟩ := hmem
  have e1 : c = c'.1 := h1.symm
  have e2 : j = j'.1 := h2.symm
  have e3 : p'.1 = p.1 := vlist_injective h3
  rw [← h4, e3]
  subst e1; subst e2; rfl

section

variable {Θ : SData m} {f : Hom (k + 1) m} {φ : Cof k} (hc : ConstOn (dataC Θ) f φ)
include hc

theorem dataC_const {n : ℕ} {h : Hom n k} (hh : (φ.restr h).holds) (r : DM n) :
    dataC (Θ.restr (f.comp (Hom.snoc h r))) = dataC (Θ.restr (f.comp (Hom.snoc h (DM.zero n)))) := by
  rw [← res_dataC, ← res_dataC]; exact hc n h hh r

theorem delem_const {n : ℕ} {h : Hom n k} (hh : (φ.restr h).holds) (r : DM n) {n' : ℕ} (g : Hom n' n) (v : V) :
    DElem Θ n' ((f.comp (Hom.snoc h r)).comp g) v ↔ DElem Θ n' ((f.comp (Hom.snoc h (DM.zero n))).comp g) v := by
  have := congrArg (fun X => El X g) (dataC_const hc hh r)
  simp only [El_dataC] at this
  rw [← mem_delemSet, ← mem_delemSet, ← delemSet_restr, ← delemSet_restr, this]

theorem ty_const {n : ℕ} {h : Hom n k} (hh : (φ.restr h).holds) (r : DM n) {c : ℕ} {C : Ctor}
    (hC : Θ.ctors[c]? = some C) {j : ℕ} (hj : j ≤ C.args.length) {G : List V} (hG : G.length = j)
    (hv : Θ.FullValid c n (f.comp (Hom.snoc h (DM.zero n))) G) :
    Θ.ty c j n (f.comp (Hom.snoc h r)) G = Θ.ty c j n (f.comp (Hom.snoc h (DM.zero n))) G := by
  have hs := congrArg (here n) (dataC_const hc hh r)
  rw [here_dataC, here_dataC, dataDatum, dataDatum, quad, quad] at hs
  simp only [pair_inj', tagZ_inj] at hs
  obtain ⟨⟨-, -, -, hs⟩, -⟩ := hs
  have hcl : c < Θ.ctors.length := (List.getElem?_eq_some_iff.1 hC).1
  have hCe : Θ.ctors[c] = C := (List.getElem?_eq_some_iff.1 hC).2
  let g0 := f.comp (Hom.snoc h (DM.zero n))
  have hp : ∀ i (hi : i < G.length), G[i] ∈ argSet (Θ.restr g0) (delemSet (Θ.restr g0)) n (Hom.id n) c
      (Θ.restr g0).ctors[c] (G.take i) i := by
    intro i hi
    unfold argSet
    have hCe' : (Θ.restr g0).ctors[c]'hcl = C := hCe
    rw [hCe']
    split
    · rename_i hr
      rw [mem_delemSet, delem_restr_iff, Hom.comp_id]
      exact hv.2 i hi (by rw [getD_ctors hC]; exact hr)
    · rename_i hr
      show G[i] ∈ El (Θ.ty c i n (g0.comp (Hom.id n)) (G.take i)) (Hom.id n)
      rw [Hom.comp_id]
      exact hv.1 i hi (by rw [getD_ctors hC]; simpa using hr)
  have := shapeV_ty (Λ1 := Θ.restr (f.comp (Hom.snoc h r))) (Λ2 := Θ.restr g0) (j := j) rfl hs hcl
    (by rw [show (Θ.restr g0).ctors[c]'hcl = C from hCe]; exact hj) ⟨G, hG, hp⟩
  simpa [SData.restr, Hom.comp_id] using this

end

end

end Model
