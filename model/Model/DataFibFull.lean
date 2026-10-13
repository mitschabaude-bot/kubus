import Model.DataTrFib

/-!
# Inductive types: the code is fibrant
-/

set_option autoImplicit false

namespace Model

open ZFSet KubusCore

noncomputable section

attribute [local instance] Classical.propDecidable

variable {k m n : ℕ}

theorem tr_restr_iff (Θ : SData m) (f : Hom k m) {n : ℕ} (g : Hom (n + 1) k) (φ : Cof n) (v w : V) :
    TR (Θ.restr f) n g φ v w ↔ TR Θ n (f.comp g) φ v w := by
  constructor
  · intro h
    induction h with
    | con hb hkv hlo hlf _ _ hpt iho ihf => exact TR.con hb hkv hlo hlf iho ihf hpt
    | hc hψ hn hka _ _ iha ihu => exact TR.hc hψ hn hka iha ihu
  · intro h
    suffices ∀ g', TR Θ n g' φ v w → ∀ g, g' = f.comp g → TR (Θ.restr f) n g φ v w from this _ h g rfl
    clear h g
    intro g' h
    induction h with
    | con hb hkv hlo hlf _ _ hpt iho ihf =>
      intro g e; subst e
      exact TR.con hb hkv hlo hlf (fun j hj hr => iho j hj hr g rfl) (fun j hj hr => ihf j hj hr _ rfl) hpt
    | hc hψ hn hka _ _ iha ihu =>
      intro g e; subst e
      exact TR.hc hψ hn hka (iha g rfl) (fun n g' r hh => ihu n g' r hh _ rfl)

theorem delem_noparams {Θ : SData m} (hΘ : Θ.Good) (hp : Θ.params = false) {n : ℕ} {g : Hom n m} {v : V}
    (hv : DElem Θ n g v) : ∀ g' : Hom n m, DElem Θ n g' v := by
  induction hv with
  | con hC hlen hrs _ hpt ih =>
    intro g'
    exact DElem.con hC hlen hrs (fun j a ha hr => ih j a ha hr g') (fun j a ha hr => by
      have := hpt j a ha hr; rwa [hΘ.const hp _ _ _ _ g'] at this)
  | hcomp hφ _ _ hcoh hbase iha ihu =>
    intro g'
    exact DElem.hcomp hφ (iha g') (fun n' h r hh => ihu n' h r hh (g'.comp h)) hcoh hbase

variable {Θ : SData m} (hΘ : Θ.Good)
include hΘ

theorem transpAt_dataC {f : Hom (k + 1) m} {φ : Cof k} {a0 : V}
    (ha : a0 ∈ El (dataC Θ) (f.comp (Hom.endpt k (DM.zero k)))) :
    transpAt (dataC Θ) f φ a0 = transpD (Θ.restr f) k (Hom.id (k + 1)) φ a0 := by
  rw [transpAt, trG, dataC, dat_mkKV, dataDatum, π1π2π2_quad, dataTr]
  rw [apZ_trGraph]
  rw [delemSet_restr]; rw [El_dataC] at ha; exact ha

theorem transpAt_dataC_eq {f : Hom (k + 1) m} {φ : Cof k} {a0 : V}
    (ha : a0 ∈ El (dataC Θ) (f.comp (Hom.endpt k (DM.zero k)))) :
    (Θ.params = false → transpAt (dataC Θ) f φ a0 = a0) ∧
    (Θ.params = true → ∀ w, TR Θ k f φ a0 w → transpAt (dataC Θ) f φ a0 = w) := by
  rw [transpAt_dataC hΘ ha]
  refine ⟨fun hp => by rw [transpD, if_pos (by simpa [SData.restr] using hp)], fun hp w hw => ?_⟩
  refine transpD_of_TR (by simpa [SData.restr] using hp) ?_
  rw [tr_restr_iff, Hom.comp_id]; exact hw

/-- **Inductive types are fibrant.** -/
theorem fib_dataC : Fib (dataC Θ) m where
  kv := isKV_dataC Θ
  elKV k f v hv := dataC_elKV f v hv
  elRes k f v hv n h := dataC_elRes hΘ.resClosed f v hv n h
  hcMem k f φ u u0 hφ hu0 hu := dataC_hcMem hφ hu0 hu
  hcFace k f φ u u0 hφ hu0 hu hh := dataC_hcFace hφ hu0 hu hh
  hcRes k f φ u u0 hφ hu0 hu n h := dataC_hcRes hΘ.resClosed hφ hu0 hu n h
  trMem n f φ a0 hφ hc ha := by
    have hd := mem_El_dataC.1 ha
    cases hp : Θ.params
    · rw [(transpAt_dataC_eq hΘ ha).1 hp]
      exact mem_El_dataC.2 (delem_noparams hΘ hp hd _)
    · obtain ⟨w, hw⟩ := hd.tr_exists hΘ φ
      rw [(transpAt_dataC_eq hΘ ha).2 hp w hw]
      exact mem_El_dataC.2 ((hw.props hΘ) hφ hc hd).1
  trFace n f φ a0 hφ hc ha hh := by
    have hd := mem_El_dataC.1 ha
    cases hp : Θ.params
    · exact (transpAt_dataC_eq hΘ ha).1 hp
    · obtain ⟨w, hw⟩ := hd.tr_exists hΘ φ
      rw [(transpAt_dataC_eq hΘ ha).2 hp w hw]
      have := ((hw.props hΘ) hφ hc hd).2.1 n (Hom.id n) (hφ.holds_restr hh _)
      rwa [res_id (hw.out_kv), res_id hd.kv] at this
  trRes n f φ a0 hφ hc ha n' h := by
    have hd := mem_El_dataC.1 ha
    have ha' : res h a0 ∈ El (dataC Θ) ((f.comp (Hom.lift h)).comp (Hom.endpt n' (DM.zero n'))) := by
      rw [Hom.comp_assoc, TranspPi.lift_comp_endpt0, ← Hom.comp_assoc]
      exact dataC_elRes hΘ.resClosed _ a0 ha n' h
    cases hp : Θ.params
    · rw [(transpAt_dataC_eq hΘ ha).1 hp, (transpAt_dataC_eq hΘ ha').1 hp]
    · obtain ⟨w, hw⟩ := hd.tr_exists hΘ φ
      rw [(transpAt_dataC_eq hΘ ha).2 hp w hw,
        (transpAt_dataC_eq hΘ ha').2 hp _ (((hw.props hΘ) hφ hc hd).2.2 n' h)]

end

end Model
