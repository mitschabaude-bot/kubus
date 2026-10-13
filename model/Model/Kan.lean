import Model.PiTransp

/-!
# Derived Kan operations

Semantic versions of the spec's defined operations `Tm.hfill`, `Tm.comp` and `Tm.transpFill`,
for any fibrant code, with their characteristic properties (typing, endpoints, behaviour on the
face, naturality).
-/

set_option autoImplicit false

namespace Model

open ZFSet

noncomputable section

attribute [local instance] Classical.propDecidable

variable {k m n n' : ℕ}

/-- The last variable at stage `k + 1`. -/
abbrev lastVar (k : ℕ) : DM (k + 1) := DM.var (Fin.last k)

theorem hcompAt_congr {c : V} {f : Hom k m} {φ : Cof k} {u u' : Tube k} {u0 : V}
    (h : ∀ n (g : Hom n k) r, (φ.restr g).holds → u n g r = u' n g r) :
    hcompAt c f φ u u0 = hcompAt c f φ u' u0 := by
  have : Tube.canon φ u = Tube.canon φ u' := by
    funext n g r; simp only [Tube.canon]; split
    · exact h n g r ‹_›
    · rfl
  simp only [hcompAt, hcKey, tubeZ, this]

theorem lastVar_restr_endpt (k : ℕ) (r : DM k) : (lastVar k).restr (Hom.endpt k r) = r := by
  ext p; simp

theorem lastVar_restr_lift (h : Hom n k) : (lastVar k).restr (Hom.lift h) = lastVar n := by
  ext p; simp

theorem lastVar_restr_snoc (h : Hom n k) (r : DM n) : (lastVar k).restr (Hom.snoc h r) = r := by
  ext p; simp

theorem DM.eq_zero_of_holds_eq0 {r : DM n} (h : (Cof.eq0 r).holds) : r = DM.zero n := by
  rw [Cof.eq0, ← DM.holds_iff_face_holds] at h
  have := DM.eq_one_of_holds h
  rw [← DM.neg_neg' r, this, DM.neg_one']

@[simp] theorem DM.min_zero_left (r : DM n) : DM.min (DM.zero n) r = DM.zero n := by ext p; simp
@[simp] theorem DM.min_one_right (r : DM n) : DM.min r (DM.one n) = r := by ext p; simp
@[simp] theorem DM.min_zero_right (r : DM n) : DM.min r (DM.zero n) = DM.zero n := by ext p; simp
@[simp] theorem DM.min_one_left (r : DM n) : DM.min (DM.one n) r = r := by ext p; simp

@[simp] theorem Cof.eq0_zero : Cof.eq0 (DM.zero n) = Cof.top n := by
  rw [Cof.eq0, DM.neg_zero']; exact Cof.eq1_one

@[simp] theorem Cof.eq0_one : Cof.eq0 (DM.one n) = Cof.bot n := by
  rw [Cof.eq0, DM.neg_one']; exact Cof.eq1_zero

theorem Cof.or_top (φ : Cof n) : (Cof.or φ (Cof.top n)).holds := Cof.holds_or.2 (Or.inr Cof.holds_top)

/-! ### `hfill` -/

/-- The face `φ ∨ i = 0` of `hfill`, at stage `k + 1`. -/
def fillFace (φ : Cof k) : Cof (k + 1) := Cof.or (φ.restr (Hom.wk k)) (Cof.eq0 (lastVar k))

/-- The tube `[φ ↦ u(i ∧ j), i = 0 ↦ u0]` of `hfill`, at stage `k + 1`. -/
def fillTube (φ : Cof k) (u : Tube k) (u0 : V) : Tube (k + 1) := fun n h r =>
  if (φ.restr ((Hom.wk k).comp h)).holds then u n ((Hom.wk k).comp h) (DM.min ((lastVar k).restr h) r)
  else res ((Hom.wk k).comp h) u0

/-- `hfill A [φ ↦ u] u0` (spec: `Tm.hfill`), at stage `k + 1`. -/
def hfillF (c : V) (f : Hom k m) (φ : Cof k) (u : Tube k) (u0 : V) : V :=
  hcompAt c (f.comp (Hom.wk k)) (fillFace φ) (fillTube φ u u0) (res (Hom.wk k) u0)

theorem isCof_fillFace {φ : Cof k} (hφ : φ.IsCof) : (fillFace φ).IsCof :=
  (hφ.restr _).or (Cof.isCof_eq0 _)

section hfill

variable {c : V} (hc : Fib c m) {f : Hom k m} {φ : Cof k} (hφ : φ.IsCof) {u : Tube k} {u0 : V}
  (hu0 : u0 ∈ El c f) (hu : TubeOK c f φ u u0)
include hc hφ hu0 hu

theorem fillTube_ok :
    TubeOK c (f.comp (Hom.wk k)) (fillFace φ) (fillTube φ u u0) (res (Hom.wk k) u0) where
  mem n h r hh := by
    simp only [fillTube]; rw [Hom.comp_assoc]; split
    · exact hu.mem _ _ _ ‹_›
    · exact hc.elRes _ _ u0 hu0 _ _
  coh n h r hh n' g := by
    simp only [fillTube]
    by_cases h1 : (φ.restr ((Hom.wk k).comp h)).holds
    · have h2 : (φ.restr ((Hom.wk k).comp (h.comp g))).holds := by
        rw [← Hom.comp_assoc, ← Cof.restr_restr]; exact Cof.IsCof.holds_restr (hφ.restr _) h1 g
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

theorem hfillF_mem : hfillF c f φ u u0 ∈ El c (f.comp (Hom.wk k)) :=
  hc.hcMem _ _ _ _ _ (isCof_fillFace hφ) (hc.elRes _ _ u0 hu0 _ _) (fillTube_ok hc hφ hu0 hu)

theorem hfillF_endpt0 : res (Hom.endpt k (DM.zero k)) (hfillF c f φ u u0) = u0 := by
  rw [hfillF, hc.hcRes _ _ _ _ _ (isCof_fillFace hφ) (hc.elRes _ _ u0 hu0 _ _) (fillTube_ok hc hφ hu0 hu),
    hc.hcFace]
  · simp only [Tube.restr, fillTube, Hom.comp_id, Hom.comp_assoc, Hom.wk_comp_endpt,
      Hom.comp_id, lastVar_restr_endpt, DM.min_zero_left]
    split
    · rw [hu.base _ _ ‹_›, res_id (hc.elKV _ _ u0 hu0)]
    · rw [res_id (hc.elKV _ _ u0 hu0)]
  · exact (isCof_fillFace hφ).restr _
  · rw [res_res, Hom.wk_comp_endpt, res_id (hc.elKV _ _ u0 hu0), Hom.comp_assoc, Hom.wk_comp_endpt,
      Hom.comp_id]; exact hu0
  · exact (fillTube_ok hc hφ hu0 hu).restr (Hom.endpt k (DM.zero k))
  · rw [fillFace, Cof.or_restr, Cof.eq0_restr, lastVar_restr_endpt, Cof.eq0_zero]; exact Cof.or_top _

theorem hfillF_endpt1 :
    res (Hom.endpt k (DM.one k)) (hfillF c f φ u u0) = hcompAt c f φ u u0 := by
  rw [hfillF, hc.hcRes _ _ _ _ _ (isCof_fillFace hφ) (hc.elRes _ _ u0 hu0 _ _) (fillTube_ok hc hφ hu0 hu),
    res_res, Hom.wk_comp_endpt, res_id (hc.elKV _ _ u0 hu0), Hom.comp_assoc, Hom.wk_comp_endpt,
    Hom.comp_id]
  have hface : (fillFace φ).restr (Hom.endpt k (DM.one k)) = φ := by
    rw [fillFace, Cof.or_restr, Cof.eq0_restr, lastVar_restr_endpt, Cof.eq0_one, Cof.or_bot,
      Cof.restr_restr, Hom.wk_comp_endpt, hφ.restr_id]
  rw [hface]
  apply hcompAt_congr
  intro n g r hg
  simp only [Tube.restr, fillTube, ← Hom.comp_assoc, Hom.wk_comp_endpt, Hom.id_comp, if_pos hg,
    ← DM.restr_restr, lastVar_restr_endpt, DM.one_restr, DM.min_one_left]

theorem hfillF_face {n : ℕ} (h : Hom n k) (hh : (φ.restr h).holds) (r : DM n) :
    res (Hom.snoc h r) (hfillF c f φ u u0) = u n h r := by
  have hface : ((fillFace φ).restr (Hom.snoc h r)).holds := by
    rw [fillFace, Cof.or_restr, Cof.holds_or]; left
    rw [Cof.restr_restr, Hom.wk_comp_snoc]; exact hh
  rw [hfillF, hc.hcRes _ _ _ _ _ (isCof_fillFace hφ) (hc.elRes _ _ u0 hu0 _ _) (fillTube_ok hc hφ hu0 hu),
    hc.hcFace _ _ _ _ _ ((isCof_fillFace hφ).restr _) _ ((fillTube_ok hc hφ hu0 hu).restr _) hface]
  · simp only [Tube.restr, fillTube, Hom.comp_id, Hom.wk_comp_snoc, if_pos hh, lastVar_restr_snoc,
      DM.min_one_right]
  · rw [res_res, Hom.comp_assoc]; exact hc.elRes _ _ u0 hu0 _ _

end hfill

theorem hfillF_res (c : V) (f : Hom k m) (φ : Cof k) (u : Tube k) (u0 : V) (h : Hom n k) :
    hcompAt c ((f.comp (Hom.wk k)).comp (Hom.lift h)) ((fillFace φ).restr (Hom.lift h))
        ((fillTube φ u u0).restr (Hom.lift h)) (res (Hom.lift h) (res (Hom.wk k) u0)) =
      hfillF c (f.comp h) (φ.restr h) (u.restr h) (res h u0) := by
  rw [hfillF, Hom.comp_assoc, Hom.wk_comp_lift, ← Hom.comp_assoc, res_res, Hom.wk_comp_lift, ← res_res]
  have hface : (fillFace φ).restr (Hom.lift h) = fillFace (φ.restr h) := by
    rw [fillFace, fillFace, Cof.or_restr, Cof.eq0_restr, lastVar_restr_lift, Cof.restr_restr,
      Cof.restr_restr, Hom.wk_comp_lift]
  rw [hface]
  congr 1
  funext n' g r
  simp only [Tube.restr, fillTube, Cof.restr_restr, ← Hom.comp_assoc, Hom.wk_comp_lift, res_res,
    ← DM.restr_restr, lastVar_restr_lift]

/-- `hfill` is natural. -/
theorem hfillF_natural {c : V} (hc : Fib c m) {f : Hom k m} {φ : Cof k} (hφ : φ.IsCof) {u : Tube k}
    {u0 : V} (hu0 : u0 ∈ El c f) (hu : TubeOK c f φ u u0) (h : Hom n k) :
    res (Hom.lift h) (hfillF c f φ u u0) = hfillF c (f.comp h) (φ.restr h) (u.restr h) (res h u0) := by
  rw [hfillF, hc.hcRes _ _ _ _ _ (isCof_fillFace hφ) (hc.elRes _ _ u0 hu0 _ _) (fillTube_ok hc hφ hu0 hu),
    hfillF_res]

end

end Model

/-! ### `comp` -/

namespace Model

open ZFSet

noncomputable section

attribute [local instance] Classical.propDecidable

variable {k m n n' : ℕ}

/-- The line `m ↦ C(r ∨ m)`, from the point `(h, r)` of the line `C` to its end. -/
def compLine (h : Hom n k) (r : DM n) : Hom (n + 1) (k + 1) :=
  Hom.snoc (h.comp (Hom.wk n)) (DM.max (r.restr (Hom.wk n)) (lastVar n))

/-- A tube in the line `c·f`: `u n h r` lies over the point `(h, r)`. -/
structure LineTubeOK (c : V) (f : Hom (k + 1) m) (ψ : Cof k) (u : Tube k) (u0 : V) : Prop where
  mem : ∀ n (h : Hom n k) r, (ψ.restr h).holds → u n h r ∈ El c (f.comp (Hom.snoc h r))
  coh : ∀ n (h : Hom n k) r, (ψ.restr h).holds → ∀ n' (g : Hom n' n),
    res g (u n h r) = u n' (h.comp g) (r.restr g)
  base : ∀ n (h : Hom n k), (ψ.restr h).holds → u n h (DM.zero n) = res h u0

/-- The tube `k ↦ transp (m. C(k ∨ m)) (k = 1) u(k)` of `comp`. -/
def compTube (c : V) (f : Hom (k + 1) m) (u : Tube k) : Tube k := fun n h r =>
  transpAt c (f.comp (compLine h r)) (Cof.eq1 r) (u n h r)

/-- `comp (i. C) [ψ ↦ u] u0` (spec: `Tm.comp`), at stage `k`. -/
def compF (c : V) (f : Hom (k + 1) m) (ψ : Cof k) (u : Tube k) (u0 : V) : V :=
  hcompAt c (f.comp (Hom.endpt k (DM.one k))) ψ (compTube c f u) (transpAt c f (Cof.bot k) u0)

theorem compLine_endpt0 (h : Hom n k) (r : DM n) :
    (compLine h r).comp (Hom.endpt n (DM.zero n)) = Hom.snoc h r := by
  apply Hom.ext_snoc <;> intro p <;> simp [compLine]

theorem compLine_endpt1 (h : Hom n k) (r : DM n) :
    (compLine h r).comp (Hom.endpt n (DM.one n)) = (Hom.endpt k (DM.one k)).comp h := by
  apply Hom.ext_snoc <;> intro p <;> simp [compLine]

theorem compLine_lift (h : Hom n k) (r : DM n) (g : Hom n' n) :
    (compLine h r).comp (Hom.lift g) = compLine (h.comp g) (r.restr g) := by
  apply Hom.ext_snoc <;> intro p <;> simp [compLine]

theorem compLine_snoc (h : Hom n k) (r : DM n) (g : Hom n' n) (x : DM n') :
    (compLine h r).comp (Hom.snoc g x) = Hom.snoc (h.comp g) (DM.max (r.restr g) x) := by
  apply Hom.ext_snoc <;> intro p <;> simp [compLine]

theorem lift_comp_compLine (h : Hom n k) (g : Hom n' n) (r : DM n') :
    (Hom.lift h).comp (compLine g r) = compLine (h.comp g) r := by
  apply Hom.ext_snoc <;> intro p <;> simp [compLine]

theorem compLine_zero (h : Hom n k) : compLine h (DM.zero n) = Hom.lift h := by
  apply Hom.ext_snoc <;> intro p <;> simp [compLine]

theorem constOn_bot (c : V) (f : Hom (k + 1) m) : ConstOn c f (Cof.bot k) :=
  fun _ _ hh => absurd hh (by simp [Cof.restr, Cof.holds, Cof.bot])

theorem constOn_compLine (c : V) (f : Hom (k + 1) m) (h : Hom n k) (r : DM n) :
    ConstOn c (f.comp (compLine h r)) (Cof.eq1 r) := by
  intro n' g hg x
  rw [Cof.eq1_restr, Cof.holds_eq1] at hg
  rw [Hom.comp_assoc, Hom.comp_assoc, compLine_snoc, compLine_snoc, DM.eq_one_of_holds hg,
    DM.max_one_left, DM.max_one_left]

theorem Cof.bot_restr (h : Hom n k) : (Cof.bot k).restr h = Cof.bot n := by
  ext p; simp [Cof.restr, Cof.bot]

section comp

variable {c : V} (hc : Fib c m) {f : Hom (k + 1) m} {ψ : Cof k} (hψ : ψ.IsCof) {u : Tube k} {u0 : V}
  (hu0 : u0 ∈ El c (f.comp (Hom.endpt k (DM.zero k)))) (hu : LineTubeOK c f ψ u u0)
include hc hψ hu0 hu

theorem compTube_ok :
    TubeOK c (f.comp (Hom.endpt k (DM.one k))) ψ (compTube c f u) (transpAt c f (Cof.bot k) u0) where
  mem n h r hh := by
    have := hc.trMem n (f.comp (compLine h r)) (Cof.eq1 r) (u n h r) (Cof.isCof_eq1 r)
      (constOn_compLine c f h r) (by rw [Hom.comp_assoc, compLine_endpt0]; exact hu.mem n h r hh)
    rwa [Hom.comp_assoc, compLine_endpt1, ← Hom.comp_assoc] at this
  coh n h r hh n' g := by
    simp only [compTube]
    rw [hc.trRes n _ _ _ (Cof.isCof_eq1 r) (constOn_compLine c f h r)
      (by rw [Hom.comp_assoc, compLine_endpt0]; exact hu.mem n h r hh) n' g,
      Hom.comp_assoc, compLine_lift, Cof.eq1_restr, hu.coh n h r hh n' g]
  base n h hh := by
    simp only [compTube]
    rw [hu.base n h hh, compLine_zero, hc.trRes k f _ u0 (Cof.isCof_bot k) (constOn_bot c f) hu0 n h,
      Cof.bot_restr]
    have : Cof.eq1 (DM.zero n) = Cof.bot n := Cof.eq1_zero
    rw [this]

theorem transp_bot_mem : transpAt c f (Cof.bot k) u0 ∈ El c (f.comp (Hom.endpt k (DM.one k))) :=
  hc.trMem k f _ u0 (Cof.isCof_bot k) (constOn_bot c f) hu0

theorem compF_mem : compF c f ψ u u0 ∈ El c (f.comp (Hom.endpt k (DM.one k))) :=
  hc.hcMem _ _ _ _ _ hψ (transp_bot_mem hc hψ hu0 hu) (compTube_ok hc hψ hu0 hu)

theorem compF_face (hh : ψ.holds) : compF c f ψ u u0 = u k (Hom.id k) (DM.one k) := by
  rw [compF, hc.hcFace _ _ _ _ _ hψ (transp_bot_mem hc hψ hu0 hu) (compTube_ok hc hψ hu0 hu) hh]
  have hid : (ψ.restr (Hom.id k)).holds := by rw [hψ.restr_id]; exact hh
  simp only [compTube]
  rw [hc.trFace k _ _ _ (Cof.isCof_eq1 _) (constOn_compLine c f _ _)
    (by rw [Hom.comp_assoc, compLine_endpt0]; exact hu.mem k _ _ hid)]
  rw [Cof.eq1_one]; exact Cof.holds_top

theorem compF_res (h : Hom n k) :
    res h (compF c f ψ u u0) = compF c (f.comp (Hom.lift h)) (ψ.restr h) (u.restr h) (res h u0) := by
  rw [compF, hc.hcRes _ _ _ _ _ hψ (transp_bot_mem hc hψ hu0 hu) (compTube_ok hc hψ hu0 hu) n h,
    compF, hc.trRes k f _ u0 (Cof.isCof_bot k) (constOn_bot c f) hu0 n h, Cof.bot_restr,
    Hom.comp_assoc, Hom.comp_assoc, ← TranspPi.lift_comp_endpt1]
  congr 1
  funext n' g r
  simp only [Tube.restr, compTube, Hom.comp_assoc, lift_comp_compLine]

end comp

end

end Model

/-! ### `transpFill` -/

namespace Model

open ZFSet

noncomputable section

attribute [local instance] Classical.propDecidable

variable {k m n n' : ℕ}

/-- The line `j ↦ A(i ∧ j)` at stage `k + 2`, for a line `A` at stage `k + 1`. -/
def tfLine (k : ℕ) : Hom (k + 2) (k + 1) :=
  Hom.snoc ((Hom.wk k).comp (Hom.wk (k + 1))) (DM.min (iVar k) (jVar k))

/-- `transpFill A φ a` (spec: `Tm.transpFill`), at stage `k + 1`: a line from `a` to
`transp A φ a`. -/
def transpFillF (c : V) (f : Hom (k + 1) m) (φ : Cof k) (a0 : V) : V :=
  transpAt c (f.comp (tfLine k)) (fillFace φ) (res (Hom.wk k) a0)

theorem tfLine_endpt0 : (tfLine k).comp (Hom.endpt (k + 1) (DM.zero _)) =
    (Hom.endpt k (DM.zero k)).comp (Hom.wk k) := by
  apply Hom.ext_snoc <;> intro p <;> simp [tfLine, iVar, jVar]

theorem tfLine_endpt1 : (tfLine k).comp (Hom.endpt (k + 1) (DM.one _)) = Hom.id (k + 1) := by
  apply Hom.ext_snoc <;> intro p <;> simp [tfLine, iVar, jVar]

theorem tfLine_snoc (h : Hom n (k + 1)) (r : DM n) :
    (tfLine k).comp (Hom.snoc h r) = Hom.snoc ((Hom.wk k).comp h) (DM.min ((lastVar k).restr h) r) := by
  apply Hom.ext_snoc <;> intro p <;> simp [tfLine, iVar, jVar]

theorem tfLine_lift_endpt1 : (tfLine k).comp (Hom.lift (Hom.endpt k (DM.one k))) = Hom.id (k + 1) := by
  apply Hom.ext_snoc <;> intro p <;> simp [tfLine, iVar, jVar]

theorem tfLine_lift_lift (h : Hom n k) :
    (tfLine k).comp (Hom.lift (Hom.lift h)) = (Hom.lift h).comp (tfLine n) := by
  apply Hom.ext_snoc <;> intro p <;> simp [tfLine, iVar, jVar]

section transpFill

variable {c : V} (hc : Fib c m) {f : Hom (k + 1) m} {φ : Cof k} (hφ : φ.IsCof)
  (hcon : ConstOn c f φ) {a0 : V} (ha : a0 ∈ El c (f.comp (Hom.endpt k (DM.zero k))))
include hc hφ hcon ha

theorem constOn_tfLine : ConstOn c (f.comp (tfLine k)) (fillFace φ) := by
  intro n h hh r
  rw [Hom.comp_assoc, Hom.comp_assoc, tfLine_snoc, tfLine_snoc]
  rw [fillFace, Cof.or_restr, Cof.holds_or] at hh
  rcases hh with hh | hh
  · rw [Cof.restr_restr] at hh
    rw [hcon _ _ hh (DM.min _ r), hcon _ _ hh (DM.min _ (DM.zero n))]
  · rw [Cof.eq0_restr] at hh
    rw [DM.eq_zero_of_holds_eq0 hh, DM.min_zero_left, DM.min_zero_left]

theorem tf_base : res (Hom.wk k) a0 ∈ El c ((f.comp (tfLine k)).comp (Hom.endpt (k + 1) (DM.zero _))) := by
  rw [Hom.comp_assoc, tfLine_endpt0, ← Hom.comp_assoc]; exact hc.elRes _ _ a0 ha _ _

theorem transpFillF_mem : transpFillF c f φ a0 ∈ El c f := by
  have := hc.trMem (k + 1) _ _ _ (isCof_fillFace hφ) (constOn_tfLine hc hφ hcon ha) (tf_base hc hφ hcon ha)
  rwa [Hom.comp_assoc, tfLine_endpt1, Hom.comp_id] at this

theorem transpFillF_endpt0 : res (Hom.endpt k (DM.zero k)) (transpFillF c f φ a0) = a0 := by
  rw [transpFillF, hc.transp_restr_face (isCof_fillFace hφ) (constOn_tfLine hc hφ hcon ha)
    (tf_base hc hφ hcon ha)]
  · rw [res_res, Hom.wk_comp_endpt, res_id (hc.elKV _ _ a0 ha)]
  · rw [fillFace, Cof.or_restr, Cof.eq0_restr, lastVar_restr_endpt, Cof.eq0_zero]; exact Cof.or_top _

theorem transpFillF_endpt1 :
    res (Hom.endpt k (DM.one k)) (transpFillF c f φ a0) = transpAt c f φ a0 := by
  rw [transpFillF, hc.trRes (k + 1) _ _ _ (isCof_fillFace hφ) (constOn_tfLine hc hφ hcon ha)
    (tf_base hc hφ hcon ha), Hom.comp_assoc, tfLine_lift_endpt1, Hom.comp_id, res_res,
    Hom.wk_comp_endpt, res_id (hc.elKV _ _ a0 ha)]
  rw [fillFace, Cof.or_restr, Cof.eq0_restr, lastVar_restr_endpt, Cof.eq0_one, Cof.or_bot,
    Cof.restr_restr, Hom.wk_comp_endpt, hφ.restr_id]

theorem transpFillF_face (h : Hom n k) (hh : (φ.restr h).holds) (r : DM n) :
    res (Hom.snoc h r) (transpFillF c f φ a0) = res h a0 := by
  rw [transpFillF, hc.transp_restr_face (isCof_fillFace hφ) (constOn_tfLine hc hφ hcon ha)
    (tf_base hc hφ hcon ha), res_res, Hom.wk_comp_snoc]
  rw [fillFace, Cof.or_restr, Cof.holds_or]; left
  rw [Cof.restr_restr, Hom.wk_comp_snoc]; exact hh

theorem transpFillF_natural (h : Hom n k) :
    res (Hom.lift h) (transpFillF c f φ a0) = transpFillF c (f.comp (Hom.lift h)) (φ.restr h) (res h a0) := by
  rw [transpFillF, hc.trRes (k + 1) _ _ _ (isCof_fillFace hφ) (constOn_tfLine hc hφ hcon ha)
    (tf_base hc hφ hcon ha) (n + 1) (Hom.lift h), transpFillF, Hom.comp_assoc, tfLine_lift_lift,
    ← Hom.comp_assoc, res_res, Hom.wk_comp_lift, ← res_res]
  congr 1
  rw [fillFace, fillFace, Cof.or_restr, Cof.eq0_restr, lastVar_restr_lift, Cof.restr_restr,
    Cof.restr_restr, Hom.wk_comp_lift]

end transpFill

end

end Model
