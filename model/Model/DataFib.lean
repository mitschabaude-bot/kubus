import Model.DataKan

/-!
# Inductive types: the code is fibrant

Element sets, restriction, and the (formal) homogeneous composition of `dataC`.
-/

set_option autoImplicit false

namespace Model

open ZFSet KubusCore

noncomputable section

attribute [local instance] Classical.propDecidable

variable {k m n : ℕ}

theorem mem_delemSet {Θ : SData m} {n : ℕ} {g : Hom n m} {v : V} : v ∈ delemSet Θ n g ↔ DElem Θ n g v := by
  rw [delemSet, ZFSet.mem_sep]
  exact ⟨fun h => h.2, fun h => ⟨delem_mem_bound h, h⟩⟩

theorem delemSet_restr (Θ : SData m) (h : Hom k m) (g : Hom n k) :
    delemSet (Θ.restr h) n g = delemSet Θ n (h.comp g) := by
  ext v; rw [mem_delemSet, mem_delemSet, delem_restr_iff]

theorem El_dataC (Θ : SData m) (f : Hom k m) : El (dataC Θ) f = delemSet Θ k f := by
  rw [dataC, El_mkKV, dataDatum, π1π2_quad, delemSet_restr, Hom.comp_id]

theorem mem_El_dataC {Θ : SData m} {f : Hom k m} {v : V} : v ∈ El (dataC Θ) f ↔ DElem Θ k f v := by
  rw [El_dataC, mem_delemSet]

theorem hcG_dataC (Θ : SData m) (f : Hom k m) :
    hcG (dataC Θ) f = hcGraph k (fun n g => delemSet Θ n (f.comp g))
      fun φ u a => hcD (Θ.restr f) k (Hom.id k) φ u a := by
  rw [dataC, hcG_mkKV, dataDatum, π2π2π2_quad]
  congr 1; funext n g; rw [delemSet_restr]

section hcomp

variable {Θ : SData m} {f : Hom k m} {φ : Cof k} {u : Tube k} {u0 : V}

theorem hcompAt_dataC_gen (hu : TubeOK (dataC Θ) f φ u u0) (hu0 : u0 ∈ El (dataC Θ) f) :
    hcompAt (dataC Θ) f φ u u0 = hcD (Θ.restr f) k (Hom.id k) φ (Tube.canon φ u) u0 := by
  rw [hcompAt, hcG_dataC, apZ_hcGraph]
  · intro n h r hh; rw [← El_dataC]; exact hu.mem n h r hh
  · rw [Hom.comp_id, ← El_dataC]; exact hu0

theorem hcompAt_dataC (hH : Θ.hit = true) (hu : TubeOK (dataC Θ) f φ u u0) (hu0 : u0 ∈ El (dataC Θ) f) :
    hcompAt (dataC Θ) f φ u u0 = hcV k φ (Tube.canon φ u) u0 := by
  rw [hcompAt_dataC_gen hu hu0, hcD, if_pos (show (Θ.restr f).hit = true from hH)]

theorem dataC_hcMem (hH : Θ.hit = true) (hφ : φ.IsCof) (hu0 : u0 ∈ El (dataC Θ) f) (hu : TubeOK (dataC Θ) f φ u u0) :
    hcompAt (dataC Θ) f φ u u0 ∈ El (dataC Θ) f := by
  rw [hcompAt_dataC hH hu hu0, mem_El_dataC]
  refine DElem.hcomp hH hφ (mem_El_dataC.1 hu0) (fun n h r hh => ?_) (fun n h r hh n' h' => ?_) (fun n h hh => ?_)
  · simp only [Tube.canon, if_pos hh]; exact mem_El_dataC.1 (hu.mem n h r hh)
  · have hh' : (φ.restr (h.comp h')).holds := by rw [← Cof.restr_restr]; exact (hφ.restr h).holds_restr hh h'
    simp only [Tube.canon, if_pos hh, if_pos hh']; exact hu.coh n h r hh n' h'
  · simp only [Tube.canon, if_pos hh]; exact hu.base n h hh

theorem dataC_hcFace (hH : Θ.hit = true) (hφ : φ.IsCof) (hu0 : u0 ∈ El (dataC Θ) f) (hu : TubeOK (dataC Θ) f φ u u0)
    (hh : φ.holds) : hcompAt (dataC Θ) f φ u u0 = u k (Hom.id k) (DM.one k) := by
  rw [hcompAt_dataC hH hu hu0]
  have hk : IsKV k (u k (Hom.id k) (DM.one k)) := (mem_El_dataC.1 (by
    have := hu.mem k (Hom.id k) (DM.one k) (hφ.holds_restr hh _); rwa [Hom.comp_id] at this)).kv
  rw [hk.eq, hcV]
  congr 1; funext n g
  have hg : (φ.restr g).holds := hφ.holds_restr hh g
  rw [if_pos hg]
  simp only [Tube.canon, if_pos hg]
  have := hu.coh k (Hom.id k) (DM.one k) (hφ.holds_restr hh _) n g
  rw [Hom.id_comp, DM.one_restr] at this
  rw [← this, here_res]

theorem dataC_hcRes (hH : Θ.hit = true) (hΘ : Θ.ResClosed) (hφ : φ.IsCof) (hu0 : u0 ∈ El (dataC Θ) f)
    (hu : TubeOK (dataC Θ) f φ u u0) (n : ℕ) (h : Hom n k) :
    res h (hcompAt (dataC Θ) f φ u u0) =
      hcompAt (dataC Θ) (f.comp h) (φ.restr h) (u.restr h) (res h u0) := by
  have hu0' : res h u0 ∈ El (dataC Θ) (f.comp h) := mem_El_dataC.2 ((mem_El_dataC.1 hu0).res hΘ n h)
  rw [hcompAt_dataC hH hu hu0, res_hcV, hcompAt, hcG_dataC, apZ_hcGraph, hcD,
    if_pos (show (Θ.restr (f.comp h)).hit = true from hH)]
  · refine hcV_congr _ fun n' h' r hh => ?_
    have hh' : (φ.restr (h.comp h')).holds := by rw [← Cof.restr_restr]; exact hh
    simp only [Tube.canon, Tube.restr, if_pos hh, if_pos hh']
  · intro n' h' r hh
    rw [Cof.restr_restr] at hh
    rw [← El_dataC]; exact hu.mem n' (h.comp h') r hh
  · rw [Hom.comp_id, ← El_dataC]; exact hu0'

end hcomp

theorem dataC_elRes {Θ : SData m} (hΘ : Θ.ResClosed) (f : Hom k m) (v : V) (hv : v ∈ El (dataC Θ) f)
    (n : ℕ) (h : Hom n k) : res h v ∈ El (dataC Θ) (f.comp h) :=
  mem_El_dataC.2 ((mem_El_dataC.1 hv).res hΘ n h)

theorem dataC_elKV {Θ : SData m} (f : Hom k m) (v : V) (hv : v ∈ El (dataC Θ) f) : IsKV k v :=
  (mem_El_dataC.1 hv).kv

end

end Model
