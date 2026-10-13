import Model.Path

/-!
# Path types are fibrant
-/

set_option autoImplicit false

namespace Model

open ZFSet

noncomputable section

attribute [local instance] Classical.propDecidable

variable {k m n n' : ℕ}

/-! ### Paths -/

/-- The line of a path: its value at the next stage. -/
def lineOf (k : ℕ) (v : V) : V := pappV (k + 1) (res (Hom.wk k) v) (lastVar k)

theorem lineOf_pathOfLine {p : V} (hp : IsKV (k + 1) p) : lineOf k (pathOfLine k p) = p := by
  rw [lineOf, res_pathOfLine, pappV_pathOfLine, res_res, Hom.lift_comp_endpt', snoc_wk_last,
    res_id hp]

theorem res_pappV_pathOfLine (p : V) (x : DM n) (g : Hom n' n) :
    res g (pappV n (pathOfLine n p) x) = pappV n' (res g (pathOfLine n p)) (x.restr g) := by
  rw [pappV_pathOfLine, res_pathOfLine, pappV_pathOfLine, res_res, res_res, Hom.endpt_comp]

theorem lift_eq_snoc (f : Hom k m) (h : Hom n (k + 1)) :
    (Hom.lift f).comp h = Hom.snoc (f.comp ((Hom.wk k).comp h)) ((lastVar k).restr h) := by
  apply Hom.ext_snoc <;> intro p <;> simp

theorem snoc_wk_lastVar (h : Hom n (k + 1)) : Hom.snoc ((Hom.wk k).comp h) ((lastVar k).restr h) = h := by
  apply Hom.ext_snoc <;> intro p <;> simp

theorem DM.zero_ne_one' : DM.zero n ≠ DM.one n := by
  intro h; have := congrArg (fun r => r.fn (Pt.allA n)) h; simp at this

section line

variable {L a0 a1 : V} (hL : Fib L (m + 1))
  (ha0 : a0 ∈ El L (Hom.endpt m (DM.zero m))) (ha1 : a1 ∈ El L (Hom.endpt m (DM.one m)))

theorem mem_pathC {f : Hom k m} {v : V} :
    v ∈ El (pathC m L a0 a1) f ↔ ∃ p ∈ El L (Hom.lift f), v = pathOfLine k p ∧
      res (Hom.endpt k (DM.zero k)) p = res f a0 ∧ res (Hom.endpt k (DM.one k)) p = res f a1 := by
  rw [El_pathC, pathElSet, mem_pathEl, El_res, Hom.comp_id]

include hL in
theorem path_line {f : Hom k m} {v : V} (hv : v ∈ El (pathC m L a0 a1) f) :
    v = pathOfLine k (lineOf k v) ∧ lineOf k v ∈ El L (Hom.lift f) ∧
      res (Hom.endpt k (DM.zero k)) (lineOf k v) = res f a0 ∧
      res (Hom.endpt k (DM.one k)) (lineOf k v) = res f a1 := by
  obtain ⟨p, hp, rfl, h0, h1⟩ := mem_pathC.1 hv
  rw [lineOf_pathOfLine (hL.elKV _ _ p hp)]
  exact ⟨rfl, hp, h0, h1⟩

include hL in
theorem path_elRes {f : Hom k m} {v : V} (hv : v ∈ El (pathC m L a0 a1) f) (h : Hom n k) :
    res h v ∈ El (pathC m L a0 a1) (f.comp h) := by
  obtain ⟨p, hp, rfl, h0, h1⟩ := mem_pathC.1 hv
  rw [res_pathOfLine, mem_pathC]
  refine ⟨res (Hom.lift h) p, ?_, rfl, ?_, ?_⟩
  · have := hL.elRes _ _ p hp _ (Hom.lift h); rwa [Hom.lift_comp] at this
  · rw [res_res, TranspPi.lift_comp_endpt0, ← res_res, h0, res_res]
  · rw [res_res, TranspPi.lift_comp_endpt1, ← res_res, h1, res_res]

/-! ### `hcomp` -/

section hcomp

variable {f : Hom k m} {φ : Cof k} (hφ : φ.IsCof) {u : Tube k} {p0 : V}
  (hp0 : p0 ∈ El (pathC m L a0 a1) f) (hu : TubeOK (pathC m L a0 a1) f φ u p0)

include hu hp0 in
theorem hcompAt_pathC :
    hcompAt (pathC m L a0 a1) f φ u p0 =
      hcompPathF k (res (Hom.lift f) L) (res f a0) (res f a1) φ (Tube.canon φ u) p0 := by
  rw [hcompAt]
  have : hcG (pathC m L a0 a1) f = pathHc k (res (Hom.lift f) L) (res f a0) (res f a1) := by
    simp [pathC, pathDatum, hcG]
  rw [this, pathHc, apZ_hcGraph]
  · intro n h r hh
    have := hu.mem n h r hh
    rwa [El_pathC, ← Hom.lift_comp, ← res_res, ← res_res, ← res_res] at this
  · rw [El_pathC] at hp0
    rwa [Hom.lift_id, res_id (isKV_res _ _), res_id (isKV_res _ _), res_id (isKV_res _ _)]

theorem lastVar_zero_of {h : Hom n (k + 1)} (h2 : ((Cof.eq0 (lastVar k)).restr h).holds) :
    (lastVar k).restr h = DM.zero n := by
  rw [Cof.eq0_restr] at h2; exact DM.eq_zero_of_holds_eq0 h2

theorem lastVar_one_of {h : Hom n (k + 1)} (h2 : ((Cof.eq1 (lastVar k)).restr h).holds) :
    (lastVar k).restr h = DM.one n := by
  rw [Cof.eq1_restr, Cof.holds_eq1] at h2; exact DM.eq_one_of_holds h2

theorem pathFace_cases {φ : Cof k} {h : Hom n (k + 1)} (hh : ((pathFace φ).restr h).holds) :
    (φ.restr ((Hom.wk k).comp h)).holds ∨ (lastVar k).restr h = DM.zero n ∨
      (lastVar k).restr h = DM.one n := by
  rw [pathFace, Cof.or_restr, Cof.or_restr, Cof.holds_or, Cof.holds_or, Cof.restr_restr] at hh
  rcases hh with hh | hh | hh
  · exact Or.inl hh
  · exact Or.inr (Or.inl (lastVar_zero_of hh))
  · exact Or.inr (Or.inr (lastVar_one_of hh))

theorem eq0_restr_holds_iff {h : Hom n (k + 1)} :
    ((Cof.eq0 (lastVar k)).restr h).holds ↔ (lastVar k).restr h = DM.zero n := by
  refine ⟨lastVar_zero_of, fun e => ?_⟩
  rw [Cof.eq0_restr, e, Cof.eq0_zero]; exact Cof.holds_top

include hL ha0 ha1 hφ hp0 hu in
theorem pathHTube_ok :
    TubeOK L (Hom.lift f) (pathFace φ) (pathHTube φ (Tube.canon φ u) (res f a0) (res f a1))
      (lineOf k p0) where
  mem n h r hh := by
    unfold pathHTube
    rw [lift_eq_snoc]
    split_ifs with h1 h2
    · rw [tube_canon_eq h1]
      obtain ⟨q, hq, hv, -, -⟩ := mem_pathC.1 (hu.mem n _ r h1)
      rw [hv, pappV_pathOfLine]
      have := hL.elRes _ _ q hq n (Hom.endpt n ((lastVar k).restr h))
      rwa [Hom.lift_comp_endpt'] at this
    · rw [lastVar_zero_of h2, snoc_zero_eq, res_res]
      exact hL.elRes _ _ a0 ha0 _ _
    · rcases pathFace_cases hh with h3 | h3 | h3
      · exact absurd h3 h1
      · exact absurd (eq0_restr_holds_iff.2 h3) h2
      · rw [h3, snoc_one_eq, res_res]
        exact hL.elRes _ _ a1 ha1 _ _
  coh n h r hh n' g := by
    unfold pathHTube
    by_cases h1 : (φ.restr ((Hom.wk k).comp h)).holds
    · have h1' : (φ.restr ((Hom.wk k).comp (h.comp g))).holds := by
        rw [← Hom.comp_assoc, ← Cof.restr_restr]; exact (hφ.restr _).holds_restr h1 g
      rw [if_pos h1, if_pos h1', tube_canon_eq h1, tube_canon_eq h1']
      obtain ⟨q, -, hv, -, -⟩ := mem_pathC.1 (hu.mem n _ r h1)
      rw [hv, res_pappV_pathOfLine, ← hv, hu.coh n _ r h1 n' g, Hom.comp_assoc, DM.restr_restr]
    · rw [if_neg h1]
      by_cases h2 : ((Cof.eq0 (lastVar k)).restr h).holds
      · rw [if_pos h2]
        have hz' : (lastVar k).restr (h.comp g) = DM.zero n' := by
          rw [← DM.restr_restr, lastVar_zero_of h2, DM.zero_restr]
        by_cases h1' : (φ.restr ((Hom.wk k).comp (h.comp g))).holds
        · rw [if_pos h1', tube_canon_eq h1', hz']
          obtain ⟨q, -, hv, hq0, -⟩ := mem_pathC.1 (hu.mem n' _ (r.restr g) h1')
          rw [hv, pappV_pathOfLine, hq0, res_res, res_res]; rfl
        · rw [if_neg h1', if_pos (eq0_restr_holds_iff.2 hz'), res_res, Hom.comp_assoc]
      · rw [if_neg h2]
        have ho : (lastVar k).restr h = DM.one n := by
          rcases pathFace_cases hh with h3 | h3 | h3
          · exact absurd h3 h1
          · exact absurd (eq0_restr_holds_iff.2 h3) h2
          · exact h3
        have ho' : (lastVar k).restr (h.comp g) = DM.one n' := by
          rw [← DM.restr_restr, ho, DM.one_restr]
        by_cases h1' : (φ.restr ((Hom.wk k).comp (h.comp g))).holds
        · rw [if_pos h1', tube_canon_eq h1', ho']
          obtain ⟨q, -, hv, -, hq1⟩ := mem_pathC.1 (hu.mem n' _ (r.restr g) h1')
          rw [hv, pappV_pathOfLine, hq1, res_res, res_res]; rfl
        · rw [if_neg h1', if_neg (by rw [eq0_restr_holds_iff, ho']; exact DM.zero_ne_one'.symm),
            res_res, Hom.comp_assoc]
  base n h hh := by
    obtain ⟨hq0, -, h00, h01⟩ := path_line hL hp0
    unfold pathHTube
    split_ifs with h1 h2
    · rw [tube_canon_eq h1, hu.base n _ h1]
      conv_lhs => rw [hq0]
      rw [res_pathOfLine, pappV_pathOfLine, res_res, Hom.lift_comp_endpt', snoc_wk_lastVar]
    · conv_rhs => rw [← snoc_wk_lastVar h]
      rw [lastVar_zero_of h2, snoc_zero_eq, ← res_res (Hom.endpt k (DM.zero k)) ((Hom.wk k).comp h), h00]
    · rcases pathFace_cases hh with h3 | h3 | h3
      · exact absurd h3 h1
      · exact absurd (eq0_restr_holds_iff.2 h3) h2
      · conv_rhs => rw [← snoc_wk_lastVar h]
        rw [h3, snoc_one_eq, ← res_res (Hom.endpt k (DM.one k)) ((Hom.wk k).comp h), h01]

theorem isCof_pathFace (hφ : φ.IsCof) : (pathFace φ).IsCof :=
  (hφ.restr _).or ((Cof.isCof_eq0 _).or (Cof.isCof_eq1 _))

theorem hcompPathF_eq (u' : Tube k) :
    hcompPathF k (res (Hom.lift f) L) (res f a0) (res f a1) φ u' p0 =
      pathOfLine k (hcompAt L (Hom.lift f) (pathFace φ) (pathHTube φ u' (res f a0) (res f a1))
        (lineOf k p0)) := by
  rw [hcompPathF, hcompAt_res_id']; rfl

include hL ha0 ha1 hφ hp0 hu in
theorem hcompPath_inner_mem :
    hcompAt L (Hom.lift f) (pathFace φ) (pathHTube φ (Tube.canon φ u) (res f a0) (res f a1))
      (lineOf k p0) ∈ El L (Hom.lift f) :=
  hL.hcMem _ _ _ _ _ (isCof_pathFace hφ) (path_line hL hp0).2.1 (pathHTube_ok hL ha0 ha1 hφ hp0 hu)

include hL ha0 ha1 hφ hp0 hu in
theorem hcompPath_inner_endpt (d : DM k) (hd : d = DM.zero k ∨ d = DM.one k) :
    res (Hom.endpt k d) (hcompAt L (Hom.lift f) (pathFace φ)
      (pathHTube φ (Tube.canon φ u) (res f a0) (res f a1)) (lineOf k p0)) =
      if d = DM.zero k then res f a0 else res f a1 := by
  have hT := pathHTube_ok hL ha0 ha1 hφ hp0 hu
  have hb := (path_line hL hp0).2.1
  rw [hL.hcRes _ _ _ _ _ (isCof_pathFace hφ) hb hT, hL.hcFace _ _ _ _ _ ((isCof_pathFace hφ).restr _)
    (hL.elRes _ _ _ hb _ _) (hT.restr _)]
  · simp only [Tube.restr, pathHTube, Hom.comp_id, Hom.wk_comp_endpt, lastVar_restr_endpt]
    have hid : ∀ x : DM k, (lastVar k).restr (Hom.endpt k x) = x := lastVar_restr_endpt k
    rcases hd with rfl | rfl
    · rw [if_pos rfl]
      split_ifs with h1
      · rw [tube_canon_eq h1]
        obtain ⟨q, -, hv, hq0, -⟩ := mem_pathC.1 (hu.mem k (Hom.id k) (DM.one k) h1)
        rw [hv, pappV_pathOfLine, hq0, Hom.comp_id]
      · rw [res_id (isKV_res _ _)]
      · exfalso; rename_i h2; exact h2 (eq0_restr_holds_iff.2 (hid _))
    · rw [if_neg DM.zero_ne_one'.symm]
      split_ifs with h1 h2
      · rw [tube_canon_eq h1]
        obtain ⟨q, -, hv, -, hq1⟩ := mem_pathC.1 (hu.mem k (Hom.id k) (DM.one k) h1)
        rw [hv, pappV_pathOfLine, hq1, Hom.comp_id]
      · exfalso; rw [eq0_restr_holds_iff, hid] at h2; exact DM.zero_ne_one' h2.symm
      · rw [res_id (isKV_res _ _)]
  · rw [pathFace, Cof.or_restr, Cof.or_restr, Cof.holds_or, Cof.holds_or, Cof.eq0_restr,
      Cof.eq1_restr, lastVar_restr_endpt]
    rcases hd with rfl | rfl
    · right; left; rw [Cof.eq0_zero]; exact Cof.holds_top
    · right; right; rw [Cof.eq1_one]; exact Cof.holds_top

include hL ha0 ha1 hφ hp0 hu in
theorem hcompPathF_mem :
    hcompPathF k (res (Hom.lift f) L) (res f a0) (res f a1) φ (Tube.canon φ u) p0 ∈
      El (pathC m L a0 a1) f := by
  rw [hcompPathF_eq, mem_pathC]
  refine ⟨_, hcompPath_inner_mem hL ha0 ha1 hφ hp0 hu, rfl, ?_, ?_⟩
  · rw [hcompPath_inner_endpt hL ha0 ha1 hφ hp0 hu _ (Or.inl rfl), if_pos rfl]
  · rw [hcompPath_inner_endpt hL ha0 ha1 hφ hp0 hu _ (Or.inr rfl), if_neg DM.zero_ne_one'.symm]

include hL ha0 ha1 hφ hp0 hu in
theorem hcompPathF_face (hh : φ.holds) :
    hcompPathF k (res (Hom.lift f) L) (res f a0) (res f a1) φ (Tube.canon φ u) p0 = u k (Hom.id k) (DM.one k) := by
  have hT := pathHTube_ok hL ha0 ha1 hφ hp0 hu
  have hb := (path_line hL hp0).2.1
  have hid : (φ.restr (Hom.id k)).holds := by rw [hφ.restr_id]; exact hh
  have hwk : (φ.restr (Hom.wk k)).holds := hφ.holds_restr hh _
  rw [hcompPathF_eq, hL.hcFace _ _ _ _ _ (isCof_pathFace hφ) hb hT
    (by rw [pathFace, Cof.holds_or]; exact Or.inl hwk)]
  simp only [pathHTube, Hom.comp_id, DM.restr_id]
  rw [if_pos hwk, tube_canon_eq hwk]
  have := hu.coh k (Hom.id k) (DM.one k) hid (k + 1) (Hom.wk k)
  rw [Hom.id_comp, DM.one_restr] at this
  rw [← this]
  have hm := hu.mem k (Hom.id k) (DM.one k) hid
  rw [Hom.comp_id] at hm
  exact (path_line hL hm).1.symm

theorem pathFace_restr_lift (h : Hom n k) : (pathFace φ).restr (Hom.lift h) = pathFace (φ.restr h) := by
  rw [pathFace, pathFace, Cof.or_restr, Cof.or_restr, Cof.eq0_restr, Cof.eq1_restr, lastVar_restr_lift,
    Cof.restr_restr, Cof.restr_restr, Hom.wk_comp_lift]

theorem pathHTube_restr_lift (u' : Tube k) (b0 b1 : V) (h : Hom n k) :
    (pathHTube φ (Tube.canon φ u') b0 b1).restr (Hom.lift h) =
      pathHTube (φ.restr h) (Tube.canon (φ.restr h) (u'.restr h)) (res h b0) (res h b1) := by
  funext n' g r
  simp only [Tube.restr, pathHTube, Tube.canon, ← Hom.comp_assoc, Hom.wk_comp_lift, Cof.restr_restr,
    ← DM.restr_restr, lastVar_restr_lift, Cof.eq0_restr, res_res]

include hL in
theorem lineOf_res {f : Hom k m} {v : V} (hv : v ∈ El (pathC m L a0 a1) f) (h : Hom n k) :
    res (Hom.lift h) (lineOf k v) = lineOf n (res h v) := by
  obtain ⟨hv', hm, -, -⟩ := path_line hL hv
  conv_rhs => rw [hv', res_pathOfLine]
  rw [lineOf_pathOfLine (isKV_res _ _)]

include hL ha0 ha1 hφ hp0 hu in
theorem hcompPathF_res (h : Hom n k) :
    res h (hcompPathF k (res (Hom.lift f) L) (res f a0) (res f a1) φ (Tube.canon φ u) p0) =
      hcompPathF n (res (Hom.lift (f.comp h)) L) (res (f.comp h) a0) (res (f.comp h) a1) (φ.restr h)
        (Tube.canon (φ.restr h) (u.restr h)) (res h p0) := by
  have hT := pathHTube_ok hL ha0 ha1 hφ hp0 hu
  have hb := (path_line hL hp0).2.1
  rw [hcompPathF_eq, hcompPathF_eq (f := f.comp h) (p0 := res h p0), res_pathOfLine,
    hL.hcRes _ _ _ _ _ (isCof_pathFace hφ) hb hT (n + 1) (Hom.lift h), Hom.lift_comp,
    pathFace_restr_lift, pathHTube_restr_lift, lineOf_res hL hp0, res_res, res_res]

end hcomp

end line

end

end Model
