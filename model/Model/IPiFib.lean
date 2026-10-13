import Model.PathFib

/-!
# Interval function types `(i : I) → A` are fibrant
-/

set_option autoImplicit false

namespace Model

open ZFSet

noncomputable section

attribute [local instance] Classical.propDecidable

variable {k m n n' : ℕ}

section line

variable {L : V} (hL : Fib L (m + 1))

theorem mem_ipiC {f : Hom k m} {v : V} :
    v ∈ El (ipiC m L) f ↔ ∃ p ∈ El L (Hom.lift f), v = pathOfLine k p := by
  rw [El_ipiC, ipiElSet, mem_ipiEl, El_res, Hom.comp_id]

include hL in
theorem ipi_line {f : Hom k m} {v : V} (hv : v ∈ El (ipiC m L) f) :
    v = pathOfLine k (lineOf k v) ∧ lineOf k v ∈ El L (Hom.lift f) := by
  obtain ⟨p, hp, rfl⟩ := mem_ipiC.1 hv
  rw [lineOf_pathOfLine (hL.elKV _ _ p hp)]
  exact ⟨rfl, hp⟩

include hL in
theorem ipi_elRes {f : Hom k m} {v : V} (hv : v ∈ El (ipiC m L) f) (h : Hom n k) :
    res h v ∈ El (ipiC m L) (f.comp h) := by
  obtain ⟨p, hp, rfl⟩ := mem_ipiC.1 hv
  rw [res_pathOfLine, mem_ipiC]
  refine ⟨res (Hom.lift h) p, ?_, rfl⟩
  have := hL.elRes _ _ p hp _ (Hom.lift h); rwa [Hom.lift_comp] at this

include hL in
theorem ipi_lineOf_res {f : Hom k m} {v : V} (hv : v ∈ El (ipiC m L) f) (h : Hom n k) :
    res (Hom.lift h) (lineOf k v) = lineOf n (res h v) := by
  obtain ⟨hv', -⟩ := ipi_line hL hv
  conv_rhs => rw [hv', res_pathOfLine]
  rw [lineOf_pathOfLine (isKV_res _ _)]

/-! ### `hcomp` -/

/-- The tube `u j` of `hcompIPi`, at stage `k + 1`. -/
def ipiHTube (u : Tube k) : Tube (k + 1) := fun n h r =>
  pappV n (u n ((Hom.wk k).comp h) r) ((lastVar k).restr h)

section hcomp

variable {f : Hom k m} {φ : Cof k} (hφ : φ.IsCof) {u : Tube k} {p0 : V}
  (hp0 : p0 ∈ El (ipiC m L) f) (hu : TubeOK (ipiC m L) f φ u p0)

include hp0 hu in
theorem hcompAt_ipiC :
    hcompAt (ipiC m L) f φ u p0 = hcompIPiF k (res (Hom.lift f) L) φ (Tube.canon φ u) p0 := by
  rw [hcompAt]
  have : hcG (ipiC m L) f = ipiHc k (res (Hom.lift f) L) := by simp [ipiC, ipiDatum, hcG]
  rw [this, ipiHc, apZ_hcGraph]
  · intro n h r hh
    have := hu.mem n h r hh
    rwa [El_ipiC, ← Hom.lift_comp, ← res_res] at this
  · rw [El_ipiC] at hp0; rwa [Hom.lift_id, res_id (isKV_res _ _)]

theorem hcompIPiF_eq (u' : Tube k) :
    hcompIPiF k (res (Hom.lift f) L) φ u' p0 =
      pathOfLine k (hcompAt L (Hom.lift f) (φ.restr (Hom.wk k)) (ipiHTube u') (lineOf k p0)) := by
  rw [hcompIPiF, hcompAt_res_id']; rfl

include hL hφ hp0 hu in
theorem ipiHTube_ok :
    TubeOK L (Hom.lift f) (φ.restr (Hom.wk k)) (ipiHTube (Tube.canon φ u)) (lineOf k p0) where
  mem n h r hh := by
    rw [Cof.restr_restr] at hh
    rw [ipiHTube, tube_canon_eq hh, lift_eq_snoc]
    obtain ⟨q, hq, hv⟩ := mem_ipiC.1 (hu.mem n _ r hh)
    rw [hv, pappV_pathOfLine]
    have := hL.elRes _ _ q hq n (Hom.endpt n ((lastVar k).restr h))
    rwa [Hom.lift_comp_endpt'] at this
  coh n h r hh n' g := by
    rw [Cof.restr_restr] at hh
    have hh' : (φ.restr ((Hom.wk k).comp (h.comp g))).holds := by
      rw [← Hom.comp_assoc, ← Cof.restr_restr]; exact (hφ.restr _).holds_restr hh g
    rw [ipiHTube, ipiHTube, tube_canon_eq hh, tube_canon_eq hh']
    obtain ⟨q, -, hv⟩ := mem_ipiC.1 (hu.mem n _ r hh)
    rw [hv, res_pappV_pathOfLine, ← hv, hu.coh n _ r hh n' g, Hom.comp_assoc, DM.restr_restr]
  base n h hh := by
    rw [Cof.restr_restr] at hh
    obtain ⟨hq0, -⟩ := ipi_line hL hp0
    rw [ipiHTube, tube_canon_eq hh, hu.base n _ hh]
    conv_lhs => rw [hq0]
    rw [res_pathOfLine, pappV_pathOfLine, res_res, Hom.lift_comp_endpt', snoc_wk_lastVar]

include hL hφ hp0 hu in
theorem hcompIPiF_mem :
    hcompIPiF k (res (Hom.lift f) L) φ (Tube.canon φ u) p0 ∈ El (ipiC m L) f := by
  rw [hcompIPiF_eq, mem_ipiC]
  exact ⟨_, hL.hcMem _ _ _ _ _ (hφ.restr _) (ipi_line hL hp0).2 (ipiHTube_ok hL hφ hp0 hu), rfl⟩

include hL hφ hp0 hu in
theorem hcompIPiF_face (hh : φ.holds) :
    hcompIPiF k (res (Hom.lift f) L) φ (Tube.canon φ u) p0 = u k (Hom.id k) (DM.one k) := by
  have hid : (φ.restr (Hom.id k)).holds := by rw [hφ.restr_id]; exact hh
  have hwk : (φ.restr (Hom.wk k)).holds := hφ.holds_restr hh _
  rw [hcompIPiF_eq, hL.hcFace _ _ _ _ _ (hφ.restr _) (ipi_line hL hp0).2 (ipiHTube_ok hL hφ hp0 hu) hwk]
  simp only [ipiHTube, Hom.comp_id, DM.restr_id]
  rw [tube_canon_eq hwk]
  have := hu.coh k (Hom.id k) (DM.one k) hid (k + 1) (Hom.wk k)
  rw [Hom.id_comp, DM.one_restr] at this
  rw [← this]
  have hm := hu.mem k (Hom.id k) (DM.one k) hid
  rw [Hom.comp_id] at hm
  exact (ipi_line hL hm).1.symm

theorem ipiHTube_restr_lift (u' : Tube k) (h : Hom n k) :
    (ipiHTube (Tube.canon φ u')).restr (Hom.lift h) = ipiHTube (Tube.canon (φ.restr h) (u'.restr h)) := by
  funext n' g r
  simp only [Tube.restr, ipiHTube, Tube.canon, ← Hom.comp_assoc, Hom.wk_comp_lift, Cof.restr_restr,
    ← DM.restr_restr, lastVar_restr_lift]

include hL hφ hp0 hu in
theorem hcompIPiF_res (h : Hom n k) :
    res h (hcompIPiF k (res (Hom.lift f) L) φ (Tube.canon φ u) p0) =
      hcompIPiF n (res (Hom.lift (f.comp h)) L) (φ.restr h) (Tube.canon (φ.restr h) (u.restr h)) (res h p0) := by
  rw [hcompIPiF_eq, hcompIPiF_eq (f := f.comp h) (p0 := res h p0), res_pathOfLine,
    hL.hcRes _ _ _ _ _ (hφ.restr _) (ipi_line hL hp0).2 (ipiHTube_ok hL hφ hp0 hu) (n + 1) (Hom.lift h),
    Hom.lift_comp, Cof.restr_restr, Hom.wk_comp_lift, ← Cof.restr_restr, ipiHTube_restr_lift,
    ipi_lineOf_res hL hp0]

end hcomp

/-! ### `transp` -/

section transp

variable {f : Hom (n + 1) m} {φ : Cof n} (hφ : φ.IsCof) (hc : ConstOn (ipiC m L) f φ)
  {p0 : V} (hp0 : p0 ∈ El (ipiC m L) (f.comp (Hom.endpt n (DM.zero n))))

include hL hp0 in
theorem transpAt_ipiC : transpAt (ipiC m L) f φ p0 = transpIPiF n (res (Hom.lift f) L) φ p0 := by
  rw [transpAt]
  have : trG (ipiC m L) f = ipiTr (n + 1) (res (Hom.lift f) L) := by simp [ipiC, ipiDatum, trG]
  rw [this]
  show apZ (trGraph n _ _) _ = _
  rw [apZ_trGraph]
  rw [El_ipiC] at hp0
  rwa [res_res, Hom.lift_comp]

theorem transpIPiF_eq :
    transpIPiF n (res (Hom.lift f) L) φ p0 =
      pathOfLine n (transpAt L ((Hom.lift f).comp (swapHom n)) (φ.restr (Hom.wk n)) (lineOf n p0)) := by
  rw [transpIPiF, transpAt_res]; rfl

include hc in
theorem ipi_constL (h : Hom n' n) (hh : (φ.restr h).holds) (r : DM n') :
    res (Hom.lift (f.comp (Hom.snoc h r))) L = res (Hom.lift (f.comp (Hom.snoc h (DM.zero n')))) L := by
  have := hc n' h hh r
  rw [res_ipiC, res_ipiC] at this
  exact ipiC_inj (isKV_res _ _) (isKV_res _ _) this

include hc in
theorem ipi_constOn : ConstOn L ((Hom.lift f).comp (swapHom n)) (φ.restr (Hom.wk n)) := by
  intro n' h hh r
  rw [Cof.restr_restr] at hh
  have e : ∀ (X : Hom n' m) (x : DM n'), res (Hom.snoc X x) L = res (Hom.endpt n' x) (res (Hom.lift X) L) := by
    intro X x; rw [res_res, Hom.lift_comp_endpt']
  rw [Hom.comp_assoc, Hom.comp_assoc, swap_comp_snoc, swap_comp_snoc, lift_comp_snoc, lift_comp_snoc,
    e, e, ipi_constL hc _ hh r]

include hL hp0 in
theorem ipi_base_mem :
    lineOf n p0 ∈ El L (((Hom.lift f).comp (swapHom n)).comp (Hom.endpt (n + 1) (DM.zero _))) := by
  rw [Hom.comp_assoc, swap_comp_endpt, lift_comp_snoc, snoc_zero_eq, ← Hom.comp_assoc]
  exact (ipi_line hL hp0).2

include hL hφ hc hp0 in
theorem transpIPiF_mem :
    transpIPiF n (res (Hom.lift f) L) φ p0 ∈ El (ipiC m L) (f.comp (Hom.endpt n (DM.one n))) := by
  rw [transpIPiF_eq, mem_ipiC]
  refine ⟨_, ?_, rfl⟩
  have := hL.trMem (n + 1) _ _ _ (hφ.restr _) (ipi_constOn hc) (ipi_base_mem hL hp0)
  rwa [Hom.comp_assoc, swap_comp_endpt, lift_comp_snoc, snoc_one_eq, ← Hom.comp_assoc] at this

include hL hφ hc hp0 in
theorem transpIPiF_face (hh : φ.holds) : transpIPiF n (res (Hom.lift f) L) φ p0 = p0 := by
  rw [transpIPiF_eq, hL.trFace (n + 1) _ _ _ (hφ.restr _) (ipi_constOn hc) (ipi_base_mem hL hp0)
    (hφ.holds_restr hh _)]
  exact (ipi_line hL hp0).1.symm

include hL hφ hc hp0 in
theorem transpIPiF_res (h : Hom n' n) :
    res h (transpIPiF n (res (Hom.lift f) L) φ p0) =
      transpIPiF n' (res (Hom.lift (f.comp (Hom.lift h))) L) (φ.restr h) (res h p0) := by
  rw [transpIPiF_eq, transpIPiF_eq (f := f.comp (Hom.lift h)) (p0 := res h p0), res_pathOfLine,
    hL.trRes (n + 1) _ _ _ (hφ.restr _) (ipi_constOn hc) (ipi_base_mem hL hp0) (n' + 1) (Hom.lift h),
    Hom.comp_assoc, swap_comp_lift_lift, ← Hom.comp_assoc, Hom.lift_comp, Cof.restr_restr,
    Hom.wk_comp_lift, ← Cof.restr_restr, ipi_lineOf_res hL hp0]

end transp

end line

/-- **Interval function types are fibrant**, with the spec's `hcompIPi` and `transpIPi`. -/
theorem fib_ipiC {L : V} (hL : Fib L (m + 1)) : Fib (ipiC m L) m where
  kv := isKV_mkKV _
  elKV k f v hv := by obtain ⟨p, -, rfl⟩ := mem_ipiC.1 hv; exact isKV_mkKV _
  elRes k f v hv n h := ipi_elRes hL hv h
  hcMem k f φ u u0 hφ hu0 hu := by
    rw [hcompAt_ipiC hu0 hu]; exact hcompIPiF_mem hL hφ hu0 hu
  hcFace k f φ u u0 hφ hu0 hu hh := by
    rw [hcompAt_ipiC hu0 hu]; exact hcompIPiF_face hL hφ hu0 hu hh
  hcRes k f φ u u0 hφ hu0 hu n h := by
    rw [hcompAt_ipiC hu0 hu, hcompAt_ipiC (ipi_elRes hL hu0 h) (hu.restr h), hcompIPiF_res hL hφ hu0 hu h]
  trMem n f φ a0 hφ hc ha := by
    rw [transpAt_ipiC hL ha]; exact transpIPiF_mem hL hφ hc ha
  trFace n f φ a0 hφ hc ha hh := by
    rw [transpAt_ipiC hL ha]; exact transpIPiF_face hL hφ hc ha hh
  trRes n f φ a0 hφ hc ha n' h := by
    have ha' : res h a0 ∈ El (ipiC m L) ((f.comp (Hom.lift h)).comp (Hom.endpt n' (DM.zero n'))) := by
      have := ipi_elRes hL ha h
      rw [Hom.comp_assoc, TranspPi.lift_comp_endpt0, ← Hom.comp_assoc]; exact this
    rw [transpAt_ipiC hL ha, transpAt_ipiC hL ha', transpIPiF_res hL hφ hc ha h]

end

end Model
