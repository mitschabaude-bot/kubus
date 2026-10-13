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

/-! ### Transport in path types -/

namespace Model

open ZFSet

noncomputable section

attribute [local instance] Classical.propDecidable

variable {k m n n' n'' : ℕ}

theorem swap_comp_snoc (h : Hom n' (n + 1)) (r : DM n') :
    (swapHom n).comp (Hom.snoc h r) = Hom.snoc (Hom.snoc ((Hom.wk n).comp h) r) ((lastVar n).restr h) := by
  apply Hom.ext_snoc
  · intro p; apply funext; intro j
    refine Fin.lastCases ?_ (fun j => ?_) j <;> simp [swapHom, iVar, jVar]
  · intro p; simp [swapHom, iVar, jVar]

theorem swap_comp_endpt (d : DM (n + 1)) :
    (swapHom n).comp (Hom.endpt (n + 1) d) = Hom.snoc (Hom.snoc (Hom.wk n) d) (lastVar n) := by
  apply Hom.ext_snoc
  · intro p; apply funext; intro j
    refine Fin.lastCases ?_ (fun j => ?_) j <;> simp [swapHom, iVar, jVar]
  · intro p; simp [swapHom, iVar, jVar]

theorem swap_comp_lift_lift (h : Hom n' n) :
    (swapHom n).comp (Hom.lift (Hom.lift h)) = (Hom.lift (Hom.lift h)).comp (swapHom n') := by
  apply Hom.ext_snoc
  · intro p; apply funext; intro j
    refine Fin.lastCases ?_ (fun j => ?_) j <;> simp [swapHom, iVar, jVar]
  · intro p; simp [swapHom, iVar, jVar]

theorem compF_res_gen (c : V) (X : Hom (k + 1) m) (Y : Hom (n + 1) (k + 1)) (ψ : Cof n) (u : Tube n)
    (u0 : V) : compF (res X c) Y ψ u u0 = compF c (X.comp Y) ψ u u0 := by
  have : compTube (res X c) Y u = compTube c (X.comp Y) u := by
    funext n' g r; simp only [compTube, transpAt, trG_res, Hom.comp_assoc]
  simp only [compF, this, hcompAt, hcG_res, transpAt, trG_res, Hom.comp_assoc]

theorem lift_comp_snoc_snoc (f : Hom (n + 1) m) (A : Hom n' n) (r x : DM n') :
    (Hom.lift f).comp (Hom.snoc (Hom.snoc A r) x) = Hom.snoc (f.comp (Hom.snoc A r)) x :=
  lift_comp_snoc f _ x

section transp

variable {L a0 a1 : V} (hL : Fib L (m + 1))
  (ha0 : a0 ∈ El L (Hom.endpt m (DM.zero m))) (ha1 : a1 ∈ El L (Hom.endpt m (DM.one m)))
  {f : Hom (n + 1) m} {φ : Cof n} (hφ : φ.IsCof) (hc : ConstOn (pathC m L a0 a1) f φ)
  {p0 : V} (hp0 : p0 ∈ El (pathC m L a0 a1) (f.comp (Hom.endpt n (DM.zero n))))

include hL hp0 in
theorem transpAt_pathC :
    transpAt (pathC m L a0 a1) f φ p0 = transpPathF n (res (Hom.lift f) L) (res f a0) (res f a1) φ p0 := by
  rw [transpAt]
  have : trG (pathC m L a0 a1) f = pathTr (n + 1) (res (Hom.lift f) L) (res f a0) (res f a1) := by
    simp [pathC, pathDatum, trG]
  rw [this]
  show apZ (trGraph n _ _) _ = _
  rw [apZ_trGraph]
  rw [El_pathC] at hp0
  rwa [res_res, res_res, res_res, Hom.lift_comp]

theorem transpPathF_eq :
    transpPathF n (res (Hom.lift f) L) (res f a0) (res f a1) φ p0 =
      pathOfLine n (compF L ((Hom.lift f).comp (swapHom n)) (pathFace φ)
        (pathTTube φ p0 (res f a0) (res f a1)) (lineOf n p0)) := by
  rw [transpPathF, compF_res_gen]; rfl

include hL ha0 ha1 hc in
theorem path_constAll (h : Hom n' n) (hh : (φ.restr h).holds) (r : DM n') :
    res (Hom.lift (f.comp (Hom.snoc h r))) L = res (Hom.lift (f.comp (Hom.snoc h (DM.zero n')))) L ∧
    res (f.comp (Hom.snoc h r)) a0 = res (f.comp (Hom.snoc h (DM.zero n'))) a0 ∧
    res (f.comp (Hom.snoc h r)) a1 = res (f.comp (Hom.snoc h (DM.zero n'))) a1 := by
  have := hc n' h hh r
  rw [res_pathC, res_pathC] at this
  exact pathC_inj (isKV_res _ _) (isKV_res _ _) (isKV_res _ _) (isKV_res _ _) (isKV_res _ _)
    (isKV_res _ _) this

include hL hp0 in
theorem pTT_phi {h : Hom n' (n + 1)} (h1 : (φ.restr ((Hom.wk n).comp h)).holds) (r : DM n') :
    pathTTube φ p0 (res f a0) (res f a1) n' h r = res h (lineOf n p0) := by
  obtain ⟨hq, hqm, -, -⟩ := path_line hL hp0
  simp only [pathTTube, if_pos h1]
  conv_lhs => rw [hq]
  rw [res_pathOfLine, pappV_pathOfLine, res_res, Hom.lift_comp_endpt', snoc_wk_lastVar]

theorem El_snoc_eq (X : Hom n' m) (x : DM n') : El L (Hom.snoc X x) = El (res (Hom.lift X) L) (Hom.endpt n' x) := by
  rw [El_res, Hom.lift_comp_endpt']

include hL ha0 ha1 hφ hc hp0 in
theorem pathTTube_ok :
    LineTubeOK L ((Hom.lift f).comp (swapHom n)) (pathFace φ) (pathTTube φ p0 (res f a0) (res f a1))
      (lineOf n p0) where
  mem n' h r hh := by
    obtain ⟨hq, hqm, hq0, hq1⟩ := path_line hL hp0
    rw [Hom.comp_assoc, swap_comp_snoc, lift_comp_snoc]
    by_cases h1 : (φ.restr ((Hom.wk n).comp h)).holds
    · rw [pTT_phi hL hp0 h1, El_snoc_eq, (path_constAll hL ha0 ha1 hc _ h1 r).1, ← El_snoc_eq]
      have := hL.elRes _ _ _ hqm _ h
      rwa [lift_eq_snoc, Hom.comp_assoc, ← snoc_zero_eq] at this
    · by_cases h2 : ((Cof.eq0 (lastVar n)).restr h).holds
      · simp only [pathTTube, if_neg h1, if_pos h2]
        rw [res_res, lastVar_zero_of h2, snoc_zero_eq]; exact hL.elRes _ _ a0 ha0 _ _
      · simp only [pathTTube, if_neg h1, if_neg h2]
        rcases pathFace_cases hh with h3 | h3 | h3
        · exact absurd h3 h1
        · exact absurd (eq0_restr_holds_iff.2 h3) h2
        · rw [res_res, h3, snoc_one_eq]; exact hL.elRes _ _ a1 ha1 _ _
  coh n' h r hh n'' g := by
    obtain ⟨hq, hqm, hq0, hq1⟩ := path_line hL hp0
    by_cases h1 : (φ.restr ((Hom.wk n).comp h)).holds
    · have h1' : (φ.restr ((Hom.wk n).comp (h.comp g))).holds := by
        rw [← Hom.comp_assoc, ← Cof.restr_restr]; exact (hφ.restr _).holds_restr h1 g
      rw [pTT_phi hL hp0 h1, pTT_phi hL hp0 h1', res_res]
    · by_cases h2 : ((Cof.eq0 (lastVar n)).restr h).holds
      · have hz' : (lastVar n).restr (h.comp g) = DM.zero n'' := by
          rw [← DM.restr_restr, lastVar_zero_of h2, DM.zero_restr]
        rw [show pathTTube φ p0 (res f a0) (res f a1) n' h r = res (Hom.snoc ((Hom.wk n).comp h) r) (res f a0)
          by simp only [pathTTube, if_neg h1, if_pos h2]]
        rw [res_res, res_res, Hom.snoc_comp, Hom.comp_assoc]
        by_cases h1' : (φ.restr ((Hom.wk n).comp (h.comp g))).holds
        · have e2 : res (h.comp g) (lineOf n p0) =
              res (f.comp (Hom.snoc ((Hom.wk n).comp (h.comp g)) (DM.zero _))) a0 := by
            conv_lhs => rw [← snoc_wk_lastVar (h.comp g), hz', snoc_zero_eq, ← res_res, hq0, res_res]
            rw [Hom.comp_assoc, ← snoc_zero_eq]
          rw [pTT_phi hL hp0 h1', e2, (path_constAll hL ha0 ha1 hc _ h1' (r.restr g)).2.1]
        · simp only [pathTTube, if_neg h1', if_pos (eq0_restr_holds_iff.2 hz'), res_res,
            Hom.comp_assoc]
      · have ho : (lastVar n).restr h = DM.one n' := by
          rcases pathFace_cases hh with h3 | h3 | h3
          · exact absurd h3 h1
          · exact absurd (eq0_restr_holds_iff.2 h3) h2
          · exact h3
        have ho' : (lastVar n).restr (h.comp g) = DM.one n'' := by
          rw [← DM.restr_restr, ho, DM.one_restr]
        rw [show pathTTube φ p0 (res f a0) (res f a1) n' h r = res (Hom.snoc ((Hom.wk n).comp h) r) (res f a1)
          by simp only [pathTTube, if_neg h1, if_neg h2]]
        rw [res_res, res_res, Hom.snoc_comp, Hom.comp_assoc]
        by_cases h1' : (φ.restr ((Hom.wk n).comp (h.comp g))).holds
        · have e2 : res (h.comp g) (lineOf n p0) =
              res (f.comp (Hom.snoc ((Hom.wk n).comp (h.comp g)) (DM.zero _))) a1 := by
            conv_lhs => rw [← snoc_wk_lastVar (h.comp g), ho', snoc_one_eq, ← res_res, hq1, res_res]
            rw [Hom.comp_assoc, ← snoc_zero_eq]
          rw [pTT_phi hL hp0 h1', e2, (path_constAll hL ha0 ha1 hc _ h1' (r.restr g)).2.2]
        · simp only [pathTTube, if_neg h1',
            if_neg (show ¬((Cof.eq0 (lastVar n)).restr (h.comp g)).holds by
              rw [eq0_restr_holds_iff, ho']; exact DM.zero_ne_one'.symm), res_res, Hom.comp_assoc]
  base n' h hh := by
    obtain ⟨hq, hqm, hq0, hq1⟩ := path_line hL hp0
    by_cases h1 : (φ.restr ((Hom.wk n).comp h)).holds
    · exact pTT_phi hL hp0 h1 _
    · by_cases h2 : ((Cof.eq0 (lastVar n)).restr h).holds
      · simp only [pathTTube, if_neg h1, if_pos h2]
        rw [res_res]
        conv_rhs => rw [← snoc_wk_lastVar h, lastVar_zero_of h2, snoc_zero_eq, ← res_res, hq0, res_res,
          Hom.comp_assoc, ← snoc_zero_eq]
      · simp only [pathTTube, if_neg h1, if_neg h2]
        have ho : (lastVar n).restr h = DM.one n' := by
          rcases pathFace_cases hh with h3 | h3 | h3
          · exact absurd h3 h1
          · exact absurd (eq0_restr_holds_iff.2 h3) h2
          · exact h3
        rw [res_res]
        conv_rhs => rw [← snoc_wk_lastVar h, ho, snoc_one_eq, ← res_res, hq1, res_res,
          Hom.comp_assoc, ← snoc_zero_eq]

include hL hp0 in
theorem pTT_base_mem :
    lineOf n p0 ∈ El L (((Hom.lift f).comp (swapHom n)).comp (Hom.endpt (n + 1) (DM.zero _))) := by
  rw [Hom.comp_assoc, swap_comp_endpt, lift_comp_snoc, snoc_zero_eq, ← Hom.comp_assoc]
  exact (path_line hL hp0).2.1

/-- The composite line of `transpPath`. -/
abbrev tpLine (L a0 a1 : V) (f : Hom (n + 1) m) (φ : Cof n) (p0 : V) : V :=
  compF L ((Hom.lift f).comp (swapHom n)) (pathFace φ) (pathTTube φ p0 (res f a0) (res f a1)) (lineOf n p0)

include hL ha0 ha1 hφ hc hp0 in
theorem tpLine_mem : tpLine L a0 a1 f φ p0 ∈ El L (Hom.lift (f.comp (Hom.endpt n (DM.one n)))) := by
  have := compF_mem hL (isCof_pathFace hφ) (pTT_base_mem hL hp0) (pathTTube_ok hL ha0 ha1 hφ hc hp0)
  rwa [Hom.comp_assoc, swap_comp_endpt, lift_comp_snoc, snoc_one_eq, ← Hom.comp_assoc] at this

theorem LineTubeOK.restr' {c : V} {F : Hom (k + 1) m} {ψ : Cof k} {u : Tube k} {u0 : V}
    (hu : LineTubeOK c F ψ u u0) (h : Hom n' k) :
    LineTubeOK c (F.comp (Hom.lift h)) (ψ.restr h) (u.restr h) (res h u0) where
  mem n'' g r hg := by
    rw [Cof.restr_restr] at hg
    rw [Hom.comp_assoc, lift_comp_snoc]; exact hu.mem n'' (h.comp g) r hg
  coh n'' g r hg n3 g' := by
    rw [Cof.restr_restr] at hg
    exact hu.coh n'' (h.comp g) r hg n3 g'
  base n'' g hg := by
    rw [Cof.restr_restr] at hg
    rw [Tube.restr, hu.base n'' (h.comp g) hg, res_res]

include hL ha0 ha1 hφ hc hp0 in
theorem tpLine_endpt (d : DM n) (hd : d = DM.zero n ∨ d = DM.one n) :
    res (Hom.endpt n d) (tpLine L a0 a1 f φ p0) =
      if d = DM.zero n then res (f.comp (Hom.endpt n (DM.one n))) a0
      else res (f.comp (Hom.endpt n (DM.one n))) a1 := by
  obtain ⟨hq, hqm, hq0, hq1⟩ := path_line hL hp0
  have hT := pathTTube_ok hL ha0 ha1 hφ hc hp0
  have hb := pTT_base_mem hL hp0
  have hh : ((pathFace φ).restr (Hom.endpt n d)).holds := by
    rw [pathFace, Cof.or_restr, Cof.or_restr, Cof.holds_or, Cof.holds_or, Cof.eq0_restr, Cof.eq1_restr,
      lastVar_restr_endpt]
    rcases hd with rfl | rfl
    · right; left; rw [Cof.eq0_zero]; exact Cof.holds_top
    · right; right; rw [Cof.eq1_one]; exact Cof.holds_top
  rw [compF_res hL (isCof_pathFace hφ) hb hT, compF_face hL ((isCof_pathFace hφ).restr _)
    (hL.transp_base_restr hb _) (hT.restr' _) hh]
  simp only [Tube.restr, Hom.comp_id]
  by_cases h1 : (φ.restr ((Hom.wk n).comp (Hom.endpt n d))).holds
  · have h1' : (φ.restr (Hom.id n)).holds := by rwa [Hom.wk_comp_endpt] at h1
    have hc1 := path_constAll hL ha0 ha1 hc (Hom.id n) h1' (DM.one n)
    rw [pTT_phi hL hp0 h1]
    rcases hd with rfl | rfl
    · rw [if_pos rfl, hq0]; exact hc1.2.1.symm
    · rw [if_neg DM.zero_ne_one'.symm, hq1]; exact hc1.2.2.symm
  · have h1' : ¬ (φ.restr (Hom.id n)).holds := by rwa [Hom.wk_comp_endpt] at h1
    simp only [pathTTube, Hom.wk_comp_endpt, if_neg h1']
    rcases hd with rfl | rfl
    · rw [if_pos (eq0_restr_holds_iff.2 (lastVar_restr_endpt _ _)), if_pos rfl, res_res]; rfl
    · rw [if_neg (by rw [eq0_restr_holds_iff, lastVar_restr_endpt]; exact DM.zero_ne_one'.symm),
        if_neg DM.zero_ne_one'.symm, res_res]; rfl

include hL ha0 ha1 hφ hc hp0 in
theorem transpPathF_mem :
    transpPathF n (res (Hom.lift f) L) (res f a0) (res f a1) φ p0 ∈
      El (pathC m L a0 a1) (f.comp (Hom.endpt n (DM.one n))) := by
  rw [transpPathF_eq, mem_pathC]
  refine ⟨_, tpLine_mem hL ha0 ha1 hφ hc hp0, rfl, ?_, ?_⟩
  · rw [tpLine_endpt hL ha0 ha1 hφ hc hp0 _ (Or.inl rfl), if_pos rfl]
  · rw [tpLine_endpt hL ha0 ha1 hφ hc hp0 _ (Or.inr rfl), if_neg DM.zero_ne_one'.symm]

include hL ha0 ha1 hφ hc hp0 in
theorem transpPathF_face (hh : φ.holds) :
    transpPathF n (res (Hom.lift f) L) (res f a0) (res f a1) φ p0 = p0 := by
  obtain ⟨hq, hqm, -, -⟩ := path_line hL hp0
  have hwk : (φ.restr (Hom.wk n)).holds := hφ.holds_restr hh _
  rw [transpPathF_eq, compF_face hL (isCof_pathFace hφ) (pTT_base_mem hL hp0)
    (pathTTube_ok hL ha0 ha1 hφ hc hp0) (by rw [pathFace, Cof.holds_or]; exact Or.inl hwk),
    pTT_phi hL hp0 (by rwa [Hom.comp_id]), res_id (hL.elKV _ _ _ hqm)]
  exact hq.symm

theorem pathTTube_restr_lift (h : Hom n' n) (b0 b1 : V) :
    (pathTTube φ p0 (res f b0) (res f b1)).restr (Hom.lift h) =
      pathTTube (φ.restr h) (res h p0) (res (f.comp (Hom.lift h)) b0) (res (f.comp (Hom.lift h)) b1) := by
  funext n'' g r
  simp only [Tube.restr, pathTTube, ← Hom.comp_assoc, Hom.wk_comp_lift, Cof.restr_restr,
    ← DM.restr_restr, lastVar_restr_lift, Cof.eq0_restr, res_res]
  simp only [Hom.comp_assoc, lift_comp_snoc]

include hL ha0 ha1 hφ hc hp0 in
theorem transpPathF_res (h : Hom n' n) :
    res h (transpPathF n (res (Hom.lift f) L) (res f a0) (res f a1) φ p0) =
      transpPathF n' (res (Hom.lift (f.comp (Hom.lift h))) L) (res (f.comp (Hom.lift h)) a0)
        (res (f.comp (Hom.lift h)) a1) (φ.restr h) (res h p0) := by
  rw [transpPathF_eq, transpPathF_eq (f := f.comp (Hom.lift h)) (p0 := res h p0), res_pathOfLine,
    compF_res hL (isCof_pathFace hφ) (pTT_base_mem hL hp0) (pathTTube_ok hL ha0 ha1 hφ hc hp0),
    Hom.comp_assoc, swap_comp_lift_lift, ← Hom.comp_assoc, Hom.lift_comp, pathFace_restr_lift,
    pathTTube_restr_lift, lineOf_res hL hp0]

end transp

/-- **Path types are fibrant**, with the spec's `hcompPath` and `transpPath`. -/
theorem fib_pathC {L a0 a1 : V} (hL : Fib L (m + 1)) (ha0 : a0 ∈ El L (Hom.endpt m (DM.zero m)))
    (ha1 : a1 ∈ El L (Hom.endpt m (DM.one m))) : Fib (pathC m L a0 a1) m where
  kv := isKV_mkKV _
  elKV k f v hv := by obtain ⟨p, -, rfl, -⟩ := mem_pathC.1 hv; exact isKV_mkKV _
  elRes k f v hv n h := path_elRes hL hv h
  hcMem k f φ u u0 hφ hu0 hu := by
    rw [hcompAt_pathC hu0 hu]; exact hcompPathF_mem hL ha0 ha1 hφ hu0 hu
  hcFace k f φ u u0 hφ hu0 hu hh := by
    rw [hcompAt_pathC hu0 hu]; exact hcompPathF_face hL ha0 ha1 hφ hu0 hu hh
  hcRes k f φ u u0 hφ hu0 hu n h := by
    rw [hcompAt_pathC hu0 hu, hcompAt_pathC (path_elRes hL hu0 h) (hu.restr h),
      hcompPathF_res hL ha0 ha1 hφ hu0 hu h]
  trMem n f φ a0' hφ hc ha := by
    rw [transpAt_pathC hL ha]; exact transpPathF_mem hL ha0 ha1 hφ hc ha
  trFace n f φ a0' hφ hc ha hh := by
    rw [transpAt_pathC hL ha]; exact transpPathF_face hL ha0 ha1 hφ hc ha hh
  trRes n f φ a0' hφ hc ha n' h := by
    have ha' : res h a0' ∈ El (pathC m L a0 a1) ((f.comp (Hom.lift h)).comp (Hom.endpt n' (DM.zero n'))) := by
      have := path_elRes hL ha h
      rw [Hom.comp_assoc, TranspPi.lift_comp_endpt0, ← Hom.comp_assoc]; exact this
    rw [transpAt_pathC hL ha, transpAt_pathC hL ha', transpPathF_res hL ha0 ha1 hφ hc ha h]

end

end Model
