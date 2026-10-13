import Model.Pi

/-!
# Π-types are fibrant

`fib_piC`: if `A` is fibrant and `B` is a fibrant family over `A`, then `Π A B` is fibrant,
with the Kan operations of the spec (`Tm.hcompPi`, `Tm.transpPi`).
-/

set_option autoImplicit false

namespace Model

open ZFSet

noncomputable section

attribute [local instance] Classical.propDecidable

variable {k m n : ℕ}

/-- `B` is a fibrant family of codes over the code `A` (at stage `m`). -/
structure FamOK (A B : V) (m : ℕ) : Prop where
  kv : IsKV m B
  graph : ∀ k (f : Hom k m), dat B k f = fnZ (El A f) (apZ (dat B k f))
  fib : ∀ k (f : Hom k m), ∀ a ∈ El A f, Fib (apZ (dat B k f) a) k
  coh : ∀ k (f : Hom k m), ∀ a ∈ El A f, ∀ n (h : Hom n k),
    res h (apZ (dat B k f) a) = apZ (dat B n (f.comp h)) (res h a)

theorem res_mem_piElSet {A B v : V} (hv : v ∈ piElSet k A B) (h : Hom n k) :
    res h v ∈ piElSet n (res h A) (res h B) := by
  simp only [piElSet, mem_piEl, El_res, dat_res] at hv ⊢
  obtain ⟨-, hfun, hcoh⟩ := hv
  refine ⟨isKV_res _ _, fun n' g => hfun n' (h.comp g), fun n' g a ha n'' h' => ?_⟩
  rw [hcoh n' (h.comp g) a ha n'' h', Hom.comp_assoc]

theorem piElSet_res_id {A B : V} (hA : IsKV k A) (hB : IsKV k B) :
    piElSet k (res (Hom.id k) A) (res (Hom.id k) B) = piElSet k A B := by
  rw [res_id hA, res_id hB]

theorem appV_mem_piElSet {A B v a : V} (hv : v ∈ piElSet k A B) (ha : a ∈ El A (Hom.id k)) :
    appV k v a ∈ El (apZ (dat B k (Hom.id k)) a) (Hom.id k) := by
  simp only [piElSet, mem_piEl] at hv
  exact (hv.2.1 k (Hom.id k)).2 a ha

/-- Application commutes with restriction. -/
theorem res_appV {A B v a : V} (hv : v ∈ piElSet k A B) (ha : a ∈ El A (Hom.id k)) (h : Hom n k) :
    res h (appV k v a) = appV n (res h v) (res h a) := by
  simp only [piElSet, mem_piEl] at hv
  rw [appV, here, hv.2.2 k (Hom.id k) a ha n h, appV_res, Hom.id_comp]

theorem TubeOK.restr {c : V} {f : Hom k m} {φ : Cof k} {u : Tube k} {u0 : V}
    (hu : TubeOK c f φ u u0) (h : Hom n k) :
    TubeOK c (f.comp h) (φ.restr h) (u.restr h) (res h u0) where
  mem n' g r hg := by
    rw [Cof.restr_restr] at hg; exact hu.mem n' (h.comp g) r hg
  coh n' g r hg n'' g' := by
    rw [Cof.restr_restr] at hg; exact hu.coh n' (h.comp g) r hg n'' g'
  base n' g hg := by
    rw [Cof.restr_restr] at hg; rw [Tube.restr, hu.base n' (h.comp g) hg, res_res]

theorem hcompAt_eq_res_id (c : V) (f : Hom k m) (φ : Cof k) (u : Tube k) (u0 : V) :
    hcompAt c f φ u u0 = hcompAt (res f c) (Hom.id k) φ u u0 := by
  simp [hcompAt, hcG_res]

theorem transpAt_eq_res_id (c : V) (f : Hom (n + 1) m) (φ : Cof n) (a0 : V) :
    transpAt c f φ a0 = transpAt (res f c) (Hom.id (n + 1)) φ a0 := by
  simp [transpAt, trG_res]

theorem tube_canon_eq {φ : Cof k} {u : Tube k} {n : ℕ} {h : Hom n k} (hh : (φ.restr h).holds)
    (r : DM n) : Tube.canon φ u n h r = u n h r := by
  simp [Tube.canon, hh]

theorem Tube.canon_restr (φ : Cof k) (u : Tube k) (h : Hom n k) :
    Tube.canon (φ.restr h) (u.restr h) = (Tube.canon φ u).restr h := by
  funext n' g r; simp only [Tube.canon, Tube.restr, Cof.restr_restr]

theorem apZ_dat_hcompPiF (A' B' : V) (φ : Cof k) (u : Tube k) (u0 : V) (g : Hom n k) {v : V}
    (hv : v ∈ El A' g) :
    apZ (dat (hcompPiF k A' B' φ u u0) n g) v =
      hcompAt (apZ (dat B' n g) v) (Hom.id n) (φ.restr g)
        (fun n' g' r => appV n' (u n' (g.comp g') r) (res g' v)) (appV n (res g u0) v) := by
  rw [hcompPiF, dat_lamV, apZ_fnZ _ hv]

theorem hcompPiF_res (A' B' : V) (φ : Cof k) (u : Tube k) (u0 : V) (h : Hom n k) :
    res h (hcompPiF k A' B' φ u u0) =
      hcompPiF n (res h A') (res h B') (φ.restr h) (u.restr h) (res h u0) := by
  simp only [hcompPiF, res_lamV, El_res, dat_res, Cof.restr_restr, res_res]
  rfl

section hcomp

variable {A B : V} (hA : Fib A m) (hB : FamOK A B m)
include hA hB

theorem hcompAt_piC {f : Hom k m} {φ : Cof k} {u : Tube k} {u0 : V}
    (hu0 : u0 ∈ El (piC m A B) f) (hu : TubeOK (piC m A B) f φ u u0) :
    hcompAt (piC m A B) f φ u u0 = hcompPiF k (res f A) (res f B) φ (Tube.canon φ u) u0 := by
  rw [hcompAt, hcG_piC, piHc, apZ_hcGraph]
  · intro n h r hh
    have := hu.mem n h r hh
    rwa [El_piC, ← res_res, ← res_res] at this
  · rw [El_piC] at hu0; rwa [res_id (isKV_res _ _), res_id (isKV_res _ _)]

/-- The data of the inner `hcomp` in `hcompPiF`. -/
theorem hcompPi_inner {f : Hom k m} {φ : Cof k} {u : Tube k} {u0 : V} (hφ : φ.IsCof)
    (hu0 : u0 ∈ El (piC m A B) f) (hu : TubeOK (piC m A B) f φ u u0)
    {n : ℕ} (g : Hom n k) {v : V} (hv : v ∈ El (res f A) g) :
    let C := apZ (dat (res f B) n g) v
    let ut : Tube n := fun n' g' r => appV n' (Tube.canon φ u n' (g.comp g') r) (res g' v)
    let b := appV n (res g u0) v
    Fib C n ∧ b ∈ El C (Hom.id n) ∧ TubeOK C (Hom.id n) (φ.restr g) ut b := by
  intro C ut b
  rw [El_res] at hv
  have hC : C = apZ (dat B n (f.comp g)) v := by simp [C]
  have hCres : ∀ n' (g' : Hom n' n), res g' C = apZ (dat B n' ((f.comp g).comp g')) (res g' v) := by
    intro n' g'; rw [hC]; exact hB.coh n (f.comp g) v hv n' g'
  have hu0' : res g u0 ∈ piElSet n (res (f.comp g) A) (res (f.comp g) B) := by
    rw [El_piC] at hu0; have := res_mem_piElSet hu0 g; rwa [res_res, res_res] at this
  have hvid : v ∈ El (res (f.comp g) A) (Hom.id n) := by rw [El_res, Hom.comp_id]; exact hv
  refine ⟨hC ▸ hB.fib n (f.comp g) v hv, ?_, ?_, ?_, ?_⟩
  · have := appV_mem_piElSet hu0' hvid
    rwa [dat_res, Hom.comp_id, ← hC] at this
  · intro n' g' r hg'
    rw [Cof.restr_restr] at hg'
    simp only [ut, tube_canon_eq hg']
    have hm := hu.mem n' (g.comp g') r hg'
    rw [El_piC, ← Hom.comp_assoc] at hm
    have hv' : res g' v ∈ El (res ((f.comp g).comp g') A) (Hom.id n') := by
      rw [El_res, Hom.comp_id]; exact hA.elRes _ _ v hv _ g'
    have := appV_mem_piElSet hm hv'
    rw [dat_res, Hom.comp_id, ← hCres, El_res, Hom.comp_id] at this
    rwa [Hom.id_comp]
  · intro n' g' r hg' n'' g''
    rw [Cof.restr_restr] at hg'
    have hg'' : (φ.restr (g.comp (g'.comp g''))).holds := by
      rw [← Hom.comp_assoc, ← Cof.restr_restr]; exact Cof.IsCof.holds_restr (hφ.restr _) hg' g''
    simp only [ut, tube_canon_eq hg', tube_canon_eq hg'']
    have hm := hu.mem n' (g.comp g') r hg'
    rw [El_piC, ← Hom.comp_assoc] at hm
    have hv' : res g' v ∈ El (res ((f.comp g).comp g') A) (Hom.id n') := by
      rw [El_res, Hom.comp_id]; exact hA.elRes _ _ v hv _ g'
    rw [res_appV hm hv' g'', hu.coh n' (g.comp g') r hg' n'' g'', res_res, Hom.comp_assoc]
  · intro n' g' hg'
    rw [Cof.restr_restr] at hg'
    simp only [ut, tube_canon_eq hg', hu.base n' (g.comp g') hg']
    have hv0 : v ∈ El (res (f.comp g) A) (Hom.id n) := hvid
    rw [res_appV hu0' hv0 g', res_res]

theorem hcompPiF_mem {f : Hom k m} {φ : Cof k} {u : Tube k} {u0 : V} (hφ : φ.IsCof)
    (hu0 : u0 ∈ El (piC m A B) f) (hu : TubeOK (piC m A B) f φ u u0) :
    hcompPiF k (res f A) (res f B) φ (Tube.canon φ u) u0 ∈ piElSet k (res f A) (res f B) := by
  apply lamV_mem_piEl
  · intro n g a ha n' h
    rw [El_res] at ha ⊢; rw [← Hom.comp_assoc]; exact hA.elRes _ _ a ha n' h
  · intro n g v hv
    obtain ⟨hC, hb, hut⟩ := hcompPi_inner hA hB hφ hu0 hu g hv
    exact hC.hcMem n (Hom.id n) _ _ _ (hφ.restr g) hb hut
  · intro n g v hv n' h
    obtain ⟨hC, hb, hut⟩ := hcompPi_inner hA hB hφ hu0 hu g hv
    rw [hC.hcRes n (Hom.id n) _ _ _ (hφ.restr g) hb hut n' h, hcompAt_eq_res_id]
    have hv' : v ∈ El A (f.comp g) := by rwa [El_res] at hv
    have hv0 : v ∈ El (res (f.comp g) A) (Hom.id n) := by rw [El_res, Hom.comp_id]; exact hv'
    have hu0' : res g u0 ∈ piElSet n (res (f.comp g) A) (res (f.comp g) B) := by
      rw [El_piC] at hu0; have := res_mem_piElSet hu0 g; rwa [res_res, res_res] at this
    congr 1
    · rw [Hom.id_comp, dat_res, dat_res, hB.coh n (f.comp g) v hv' n' h, Hom.comp_assoc]
    · rw [Cof.restr_restr]
    · funext n'' g' r; simp only [Tube.restr, res_res, Hom.comp_assoc]
    · rw [res_appV hu0' hv0 h, res_res]

theorem hcompPiF_face {f : Hom k m} {φ : Cof k} {u : Tube k} {u0 : V} (hφ : φ.IsCof)
    (hu0 : u0 ∈ El (piC m A B) f) (hu : TubeOK (piC m A B) f φ u u0) (hh : φ.holds) :
    hcompPiF k (res f A) (res f B) φ (Tube.canon φ u) u0 = u k (Hom.id k) (DM.one k) := by
  have hmem := hcompPiF_mem hA hB hφ hu0 hu
  have hid : (φ.restr (Hom.id k)).holds := by rw [hφ.restr_id]; exact hh
  have hu1 : u k (Hom.id k) (DM.one k) ∈ piElSet k (res f A) (res f B) := by
    have := hu.mem k (Hom.id k) (DM.one k) hid; rwa [Hom.comp_id, El_piC] at this
  refine piEl_ext (D := fun _ g => El (res f A) g) hmem hu1 fun n g v hv => ?_
  obtain ⟨hC, hb, hut⟩ := hcompPi_inner hA hB hφ hu0 hu g hv
  have hg : (φ.restr g).holds := hφ.holds_restr hh g
  rw [apZ_dat_hcompPiF _ _ _ _ _ _ hv, hC.hcFace n (Hom.id n) _ _ _ (hφ.restr g) hb hut hg]
  have hg' : (φ.restr (g.comp (Hom.id n))).holds := by rw [Hom.comp_id]; exact hg
  have hv' : v ∈ El A (f.comp g) := by simpa [El_res] using hv
  simp only [Hom.comp_id]
  rw [tube_canon_eq hg, res_id (hA.elKV _ _ v hv'), ← appV_res, hu.coh k (Hom.id k) (DM.one k) hid n g, Hom.id_comp, DM.one_restr]

end hcomp

end

end Model
