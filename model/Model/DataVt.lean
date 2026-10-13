import Model.DataRestr

/-!
# Inductive types: data codes are small

The code of an inductive type is in `Vt l` when its argument types are (its parameters are not
recorded, so large parameters are no obstacle).
-/

set_option autoImplicit false

namespace Model

open ZFSet KubusCore

noncomputable section

attribute [local instance] Classical.propDecidable

variable {l k m n : ℕ} (hl : l ≤ 4)
include hl

theorem vlist_elems_mem_Vt : ∀ {as : List V}, vlist as ∈ Vt l → ∀ a ∈ as, a ∈ Vt l
  | [], _ => by simp
  | a :: as, h => by
    simp only [vlist] at h
    have h1 := π1_mem_Vt hl h; have h2 := π2_mem_Vt hl h
    simp only [π1_pair, π2_pair] at h1 h2
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact h1
    · exact vlist_elems_mem_Vt h2 x hx

theorem conV_args_mem_Vt {ctors : List Ctor} {c : ℕ} {args : List V} {rs : List (DM k)}
    (hb : bndAtMap (ctors.getD c default) rs (Hom.id k) = none) (hkv : ∀ a ∈ args, IsKV k a)
    (h : conV ctors k c args rs ∈ Vt l) : ∀ a ∈ args, a ∈ Vt l := by
  have := here_mem_Vt hl h (m := k)
  rw [here_conV hb, map_res_id_of_kv hkv] at this
  have h2 := π2_mem_Vt hl this
  simp only [tagZ, π2_pair] at h2
  have h3 := π1_mem_Vt hl (π2_mem_Vt hl h2)
  simp only [π2_pair, π1_pair] at h3
  exact vlist_elems_mem_Vt hl h3

theorem hcV_parts_mem_Vt {ψ : Cof k} {u : Tube k} {a : V} (hψ : ψ.IsCof) (hn : ¬ ψ.holds) (hka : IsKV k a)
    (h : hcV k ψ u a ∈ Vt l) : a ∈ Vt l ∧ ∀ n (g : Hom n k) r, (ψ.restr g).holds → u n g r ∈ Vt l := by
  have := here_mem_Vt hl h (m := k)
  rw [here_hcV hn, hψ.restr_id] at this
  have h2 := π2_mem_Vt hl (π2_mem_Vt hl this)
  simp only [tagZ, π2_pair] at h2
  refine ⟨?_, fun n g r hg => ?_⟩
  · have := π2_mem_Vt hl h2; simp only [π2_pair] at this; rwa [res_id hka] at this
  · have ht := π1_mem_Vt hl h2
    simp only [π1_pair] at ht
    have := apZ_mem_Vt hl ht (enc (⟨n, g, r⟩ : TubeDom k))
    rw [tubeZ] at this
    change apC (fnC _) _ ∈ Vt l at this
    rw [apC_fnC] at this
    simpa [Tube.canon, Tube.restr, Hom.id_comp, if_pos hg] using this

theorem TR.out_mem_Vt {Θ : SData m} (hty : ∀ c j n g pre, Θ.ty c j n g pre ∈ Vt l) {k : ℕ} {f : Hom (k + 1) m}
    {φ : Cof k} {v w : V} (htr : TR Θ k f φ v w) (hv : v ∈ Vt l) : w ∈ Vt l := by
  induction htr with
  | @con k f φ c args rs outs fills hb hkv hlo hlf hro hrf hpt iho ihf =>
    have ha := conV_args_mem_Vt hl hb hkv hv
    refine conV_mem_Vt hl _ _ _ fun o ho => ?_
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ho
    have e : outs[j] = outs.getD j ∅ := List.getElem_eq_getD ∅
    rw [e]
    cases hr : (Θ.ctors.getD c default).isRec j
    · rw [(hpt j (by omega) hr).1]; exact transpAt_mem_Vt hl (hty _ _ _ _ _) _ _ _
    · exact iho j (by omega) hr (ha _ (List.getElem_mem _))
  | @hc k f φ ψ u u' a a' hψ hn hka ha htu iha ihu =>
    obtain ⟨hav, huv⟩ := hcV_parts_mem_Vt hl hψ hn hka hv
    exact hcV_mem_Vt hl (fun n g r hg => ihu n g r hg (huv n g r hg)) (iha hav)

theorem HR.out_mem_Vt {Θ : SData m} (hty : ∀ c j n g pre, Θ.ty c j n g pre ∈ Vt l) {k : ℕ} {g : Hom k m}
    {φ : Cof k} {u : Tube k} {v w : V} (hr : HR Θ k g φ u v w) (hv : v ∈ Vt l) : w ∈ Vt l := by
  induction hr with
  | con hb hkv hu hlo hlf hro hpt iho =>
    rename_i c args outs fills ua
    have ha := conV_args_mem_Vt hl hb hkv hv
    refine conV_mem_Vt hl _ _ _ fun o ho => ?_
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ho
    have e : outs[j] = outs.getD j ∅ := List.getElem_eq_getD ∅
    rw [e]
    cases hr : (Θ.ctors.getD c default).isRec j
    · rw [(hpt j (by omega) hr).1]; exact compF_mem_Vt hl (hty _ _ _ _ _) _ _ _ _
    · exact iho j (by omega) hr (ha _ (List.getElem_mem _))

theorem dataC_mem_Vt {Θ : SData m} (hty : ∀ c j n g pre, Θ.ty c j n g pre ∈ Vt l) (hpv : ∀ n g, Θ.pv n g ∈ Vt l) :
    dataC Θ ∈ Vt l := by
  refine mkKV_mem_Vt hl fun k f => ?_
  set Λ := Θ.restr f
  have htyΛ : ∀ c j n g pre, (∀ a ∈ pre, a ∈ Vt l) → Λ.ty c j n g pre ∈ Vt l := fun c j n g pre _ => hty _ _ _ _ _
  have hD : ∀ n g, delemSet Λ n g ∈ Vt l := fun n g => sep_mem_Vt (dataBound_mem_Vt hl htyΛ n g) _
  refine quad_mem_Vt (tagZ_mem_Vt (pair_mem_Vt (natZ_mem_Vt hl _) (pair_mem_Vt (hpv _ _) ?_))) (hD k (Hom.id k)) ?_
    (hcGraph_mem_Vt hl hD fun φ u u0 hu hu0 => ?_)
  · refine iUnion_mem_Vt IsSmallAt.of_countable (fun c => iUnion_mem_Vt IsSmallAt.of_countable (fun j => ?_) hl) hl
    haveI := vpref_small5 (Θ := Λ) (Y := delemSet Λ) (n := k) (g := Hom.id k) (c := c) (C := Λ.ctors[c]) j
    refine range_mem_Vt' (vpref_small hl hD htyΛ j).2 (fun p => ?_) hl
    refine pair_mem_Vt (natZ_mem_Vt hl _) (pair_mem_Vt (natZ_mem_Vt hl _) (pair_mem_Vt ?_ (hty _ _ _ _ _)))
    refine vlist_mem_Vt hl fun a ha => ?_
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
    exact vpref_mem_Vt hl hD htyΛ p.2.2 i hi
  · cases k with
    | zero => exact empty_mem_Vt hl
    | succ n =>
      refine trGraph_mem_Vt hl (hD n _) fun φ a ha => ?_
      have hav : a ∈ Vt l := Vt_trans l (hD n _) ha
      unfold transpD; split
      · exact hav
      · split
        · exact TR.out_mem_Vt hl (Θ := Λ) (fun c j n g pre => hty _ _ _ _ _) (Classical.choose_spec ‹∃ w, _›) hav
        · exact hav
  · unfold hcD; split
    · exact hcV_mem_Vt hl (fun n h r _ => hu n h r) hu0
    · split
      · exact HR.out_mem_Vt hl (Θ := Λ) (fun c j n g pre => hty _ _ _ _ _) (Classical.choose_spec ‹∃ w, _›) hu0
      · exact hu0

end

end Model
