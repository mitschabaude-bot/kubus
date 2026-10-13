import Model.Kan

/-!
# The filler of heterogeneous composition

`fillF c f ψ u u0` (spec: `Tm.fill`): at stage `k + 1` (the last variable `i`), the composition
along `j` of the line `C(i ∧ j)` with the system `[ψ ↦ u(i ∧ j), i = 0 ↦ u0]`. It is a line in
`C` from `u0` to `comp C [ψ ↦ u] u0` that agrees with `u` on `ψ`.
-/

set_option autoImplicit false

namespace Model

open ZFSet

noncomputable section

attribute [local instance] Classical.propDecidable

variable {k m n n' : ℕ}

def fillF (c : V) (f : Hom (k + 1) m) (ψ : Cof k) (u : Tube k) (u0 : V) : V :=
  compF c (f.comp (tfLine k)) (fillFace ψ) (fillTube ψ u u0) (res (Hom.wk k) u0)

theorem LineTubeOK.restr {c : V} {f : Hom (k + 1) m} {ψ : Cof k} {u : Tube k} {u0 : V}
    (hu : LineTubeOK c f ψ u u0) (h : Hom n k) :
    LineTubeOK c (f.comp (Hom.lift h)) (ψ.restr h) (u.restr h) (res h u0) where
  mem n' g r hg := by
    rw [Cof.restr_restr] at hg
    have := hu.mem n' (h.comp g) r hg
    rwa [Hom.comp_assoc, lift_comp_snoc]
  coh n' g r hg n'' g' := by rw [Cof.restr_restr] at hg; exact hu.coh n' (h.comp g) r hg n'' g'
  base n' g hg := by
    rw [Cof.restr_restr] at hg; simp only [Tube.restr]; rw [hu.base n' (h.comp g) hg, res_res]

section fill

variable {c : V} (hc : Fib c m) {f : Hom (k + 1) m} {ψ : Cof k} (hψ : ψ.IsCof) {u : Tube k} {u0 : V}
  (hu0 : u0 ∈ El c (f.comp (Hom.endpt k (DM.zero k)))) (hu : LineTubeOK c f ψ u u0)
include hc hψ hu0 hu

theorem fillTube_lineOK :
    LineTubeOK c (f.comp (tfLine k)) (fillFace ψ) (fillTube ψ u u0) (res (Hom.wk k) u0) where
  mem n h r hh := by
    rw [Hom.comp_assoc, tfLine_snoc]
    simp only [fillTube]; split
    · exact hu.mem _ _ _ ‹_›
    · rename_i h1
      have h0 : (lastVar k).restr h = DM.zero n := by
        rw [fillFace, Cof.or_restr, Cof.holds_or] at hh
        rcases hh with hh | hh
        · exact absurd (by rwa [Cof.restr_restr] at hh) h1
        · rw [Cof.eq0_restr] at hh; exact DM.eq_zero_of_holds_eq0 hh
      rw [h0, DM.min_zero_left, snoc_zero_eq, ← Hom.comp_assoc]
      exact hc.elRes _ _ u0 hu0 _ _
  coh n h r hh n' g := by
    simp only [fillTube]
    by_cases h1 : (ψ.restr ((Hom.wk k).comp h)).holds
    · have h2 : (ψ.restr ((Hom.wk k).comp (h.comp g))).holds := by
        rw [← Hom.comp_assoc, ← Cof.restr_restr]; exact Cof.IsCof.holds_restr (hψ.restr _) h1 g
      rw [if_pos h1, if_pos h2, hu.coh _ _ _ h1, Hom.comp_assoc, DM.min_restr, DM.restr_restr]
    · rw [if_neg h1]
      have h0 : (lastVar k).restr h = DM.zero n := by
        rw [fillFace, Cof.or_restr, Cof.holds_or] at hh
        rcases hh with hh | hh
        · exact absurd (by rwa [Cof.restr_restr] at hh) h1
        · rw [Cof.eq0_restr] at hh; exact DM.eq_zero_of_holds_eq0 hh
      split
      · rw [← DM.restr_restr, h0, DM.zero_restr, DM.min_zero_left, hu.base _ _ ‹_›, res_res,
          Hom.comp_assoc]
      · rw [res_res, Hom.comp_assoc]
  base n h hh := by
    simp only [fillTube]; split
    · rw [DM.min_zero_right, hu.base _ _ ‹_›, res_res]
    · rw [res_res]

omit hψ hu in
theorem fill_base : res (Hom.wk k) u0 ∈ El c ((f.comp (tfLine k)).comp (Hom.endpt (k + 1) (DM.zero _))) := by
  rw [Hom.comp_assoc, tfLine_endpt0, ← Hom.comp_assoc]; exact hc.elRes _ _ u0 hu0 _ _

theorem fillF_mem : fillF c f ψ u u0 ∈ El c f := by
  have := compF_mem hc (isCof_fillFace hψ) (fill_base hc hu0) (fillTube_lineOK hc hψ hu0 hu)
  rwa [Hom.comp_assoc, tfLine_endpt1, Hom.comp_id] at this

theorem fillF_res (h : Hom n (k + 1)) :
    res h (fillF c f ψ u u0) = compF c ((f.comp (tfLine k)).comp (Hom.lift h)) ((fillFace ψ).restr h)
      ((fillTube ψ u u0).restr h) (res h (res (Hom.wk k) u0)) :=
  compF_res hc (isCof_fillFace hψ) (fill_base hc hu0) (fillTube_lineOK hc hψ hu0 hu) h

theorem fillF_face (h : Hom n k) (hh : (ψ.restr h).holds) (r : DM n) :
    res (Hom.snoc h r) (fillF c f ψ u u0) = u n h r := by
  have hface : ((fillFace ψ).restr (Hom.snoc h r)).holds := by
    rw [fillFace, Cof.or_restr, Cof.holds_or]; left
    rw [Cof.restr_restr, Hom.wk_comp_snoc]; exact hh
  rw [fillF_res hc hψ hu0 hu, compF_face hc ((isCof_fillFace hψ).restr _) _
    ((fillTube_lineOK hc hψ hu0 hu).restr _) hface]
  · simp only [Tube.restr, fillTube, Hom.comp_id, Hom.wk_comp_snoc, if_pos hh, lastVar_restr_snoc,
      DM.min_one_right]
  · have := hc.elRes _ _ _ (fill_base hc hu0) _ (Hom.snoc h r)
    rw [res_res] at this ⊢
    rwa [Hom.comp_assoc (f.comp (tfLine k)), TranspPi.lift_comp_endpt0, ← Hom.comp_assoc]

theorem fillF_endpt0 : res (Hom.endpt k (DM.zero k)) (fillF c f ψ u u0) = u0 := by
  have hface : ((fillFace ψ).restr (Hom.endpt k (DM.zero k))).holds := by
    rw [fillFace, Cof.or_restr, Cof.eq0_restr, lastVar_restr_endpt, Cof.eq0_zero]; exact Cof.or_top _
  rw [fillF_res hc hψ hu0 hu, compF_face hc ((isCof_fillFace hψ).restr _) _
    ((fillTube_lineOK hc hψ hu0 hu).restr _) hface]
  · simp only [Tube.restr, fillTube, Hom.comp_id, Hom.wk_comp_endpt, lastVar_restr_endpt, DM.min_zero_left]
    split
    · rw [hu.base _ _ ‹_›, res_id (hc.elKV _ _ u0 hu0)]
    · rw [res_id (hc.elKV _ _ u0 hu0)]
  · have := hc.elRes _ _ _ (fill_base hc hu0) _ (Hom.endpt k (DM.zero k))
    rw [res_res] at this ⊢
    rwa [Hom.comp_assoc (f.comp (tfLine k)), TranspPi.lift_comp_endpt0, ← Hom.comp_assoc]

theorem fillF_endpt1 : res (Hom.endpt k (DM.one k)) (fillF c f ψ u u0) = compF c f ψ u u0 := by
  rw [fillF_res hc hψ hu0 hu, Hom.comp_assoc, tfLine_lift_endpt1, Hom.comp_id, res_res, Hom.wk_comp_endpt,
    res_id (hc.elKV _ _ u0 hu0)]
  have hface : (fillFace ψ).restr (Hom.endpt k (DM.one k)) = ψ := by
    rw [fillFace, Cof.or_restr, Cof.eq0_restr, lastVar_restr_endpt, Cof.eq0_one, Cof.or_bot,
      Cof.restr_restr, Hom.wk_comp_endpt, hψ.restr_id]
  rw [hface]
  apply compF_congr
  intro n g r hg
  simp only [Tube.restr, fillTube, ← Hom.comp_assoc, Hom.wk_comp_endpt, Hom.id_comp, if_pos hg,
    ← DM.restr_restr, lastVar_restr_endpt, DM.one_restr, DM.min_one_left]

theorem fillF_natural (h : Hom n k) :
    res (Hom.lift h) (fillF c f ψ u u0) = fillF c (f.comp (Hom.lift h)) (ψ.restr h) (u.restr h) (res h u0) := by
  rw [fillF_res hc hψ hu0 hu, fillF, Hom.comp_assoc, tfLine_lift_lift, ← Hom.comp_assoc, res_res,
    Hom.wk_comp_lift, ← res_res]
  have hface : (fillFace ψ).restr (Hom.lift h) = fillFace (ψ.restr h) := by
    rw [fillFace, fillFace, Cof.or_restr, Cof.eq0_restr, lastVar_restr_lift, Cof.restr_restr,
      Cof.restr_restr, Hom.wk_comp_lift]
  rw [hface]
  congr 1
  funext n' g r
  simp only [Tube.restr, fillTube, Cof.restr_restr, ← Hom.comp_assoc, Hom.wk_comp_lift, res_res,
    ← DM.restr_restr, lastVar_restr_lift]

end fill

end

end Model
