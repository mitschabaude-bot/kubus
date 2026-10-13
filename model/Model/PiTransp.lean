import Model.PiFib
import Model.CubeLemmas

/-!
# Transport in Π-types is lawful

The semantic `Tm.transpPi`: typing, boundary and naturality.
-/

set_option autoImplicit false

namespace Model

open ZFSet

noncomputable section

attribute [local instance] Classical.propDecidable

variable {k m n n' n'' : ℕ}

namespace TranspPi

/-- The line `j ↦ A(i ∨ ~j)` at stage `n' + 2`, for `g : Hom n' n`. -/
def γ (g : Hom n' n) : Hom (n' + 2) (n + 1) :=
  Hom.snoc (g.comp ((Hom.wk n').comp (Hom.wk (n' + 1)))) (DM.max (iVar n') (DM.neg (jVar n')))

/-- The face `φ ∨ i = 1` at stage `n' + 1`. -/
def ψ (φ : Cof n) (g : Hom n' n) : Cof (n' + 1) :=
  Cof.or (φ.restr (g.comp (Hom.wk n'))) (Cof.eq1 (DM.var (Fin.last n')))

/-- The line `j ↦ A(~j)` at stage `n' + 1`. -/
def γ0 (g : Hom n' n) : Hom (n' + 1) (n + 1) := Hom.snoc (g.comp (Hom.wk n')) (DM.neg (DM.var (Fin.last n')))

/-- `w(i)`, at stage `n' + 1`. -/
def w (A : V) (φ : Cof n) (g : Hom n' n) (v : V) : V := transpAt A (γ g) (ψ φ g) (res (Hom.wk n') v)

/-- `w0`, at stage `n'`. -/
def w0 (A : V) (φ : Cof n) (g : Hom n' n) (v : V) : V := transpAt A (γ0 g) (φ.restr g) v

/-- The codomain line `i ↦ B[w(i)]`, at stage `n' + 1`. -/
def C (A B : V) (φ : Cof n) (g : Hom n' n) (v : V) : V := apZ (dat B (n' + 1) (Hom.lift g)) (w A φ g v)

theorem apZ_dat_transpPiF (A B : V) (φ : Cof n) (u0 : V) (g : Hom n' n) {v : V}
    (hv : v ∈ El A ((Hom.endpt n (DM.one n)).comp g)) :
    apZ (dat (transpPiF n A B φ u0) n' g) v =
      transpAt (C A B φ g v) (Hom.id (n' + 1)) (φ.restr g) (appV n' (res g u0) (w0 A φ g v)) := by
  rw [transpPiF, dat_lamV, apZ_fnZ _ hv]; rfl

/-! ### Cube map identities -/

theorem γ_endpt0 (g : Hom n' n) :
    (γ g).comp (Hom.endpt (n' + 1) (DM.zero _)) = ((Hom.endpt n (DM.one n)).comp g).comp (Hom.wk n') := by
  apply Hom.ext_snoc <;> intro p <;> simp [γ, iVar, jVar]

theorem γ_endpt1 (g : Hom n' n) : (γ g).comp (Hom.endpt (n' + 1) (DM.one _)) = Hom.lift g := by
  apply Hom.ext_snoc <;> intro p <;> simp [γ, iVar, jVar]

theorem γ0_endpt0 (g : Hom n' n) : (γ0 g).comp (Hom.endpt n' (DM.zero _)) = (Hom.endpt n (DM.one n)).comp g := by
  apply Hom.ext_snoc <;> intro p <;> simp [γ0]

theorem γ0_endpt1 (g : Hom n' n) : (γ0 g).comp (Hom.endpt n' (DM.one _)) = (Hom.endpt n (DM.zero n)).comp g := by
  apply Hom.ext_snoc <;> intro p <;> simp [γ0]

theorem γ_lift_endpt0 (g : Hom n' n) : (γ g).comp (Hom.lift (Hom.endpt n' (DM.zero _))) = γ0 g := by
  apply Hom.ext_snoc <;> intro p <;> simp [γ, γ0, iVar, jVar]

theorem γ_lift_endpt1 (g : Hom n' n) :
    (γ g).comp (Hom.lift (Hom.endpt n' (DM.one _))) = Hom.snoc (g.comp (Hom.wk n')) (DM.one _) := by
  apply Hom.ext_snoc <;> intro p <;> simp [γ, iVar, jVar]

theorem γ_comp_snoc (g : Hom n' n) (h : Hom n'' (n' + 1)) (r : DM n'') :
    (γ g).comp (Hom.snoc h r) =
      Hom.snoc ((g.comp (Hom.wk n')).comp h) (DM.max ((DM.var (Fin.last n')).restr h) (DM.neg r)) := by
  apply Hom.ext_snoc <;> intro p <;> simp [γ, iVar, jVar]

theorem γ0_comp_snoc (g : Hom n' n) (h : Hom n'' n') (r : DM n'') :
    (γ0 g).comp (Hom.snoc h r) = Hom.snoc (g.comp h) (DM.neg r) := by
  apply Hom.ext_snoc <;> intro p <;> simp [γ0]

theorem γ_comp_lift_lift (g : Hom n' n) (h : Hom n'' n') :
    (γ g).comp (Hom.lift (Hom.lift h)) = γ (g.comp h) := by
  apply Hom.ext_snoc <;> intro p <;> simp [γ, iVar, jVar]

theorem γ0_comp_lift (g : Hom n' n) (h : Hom n'' n') : (γ0 g).comp (Hom.lift h) = γ0 (g.comp h) := by
  apply Hom.ext_snoc <;> intro p <;> simp [γ0]

theorem lift_comp_γ (h : Hom n'' n) (g : Hom n' n'') : (Hom.lift h).comp (γ g) = γ (h.comp g) := by
  apply Hom.ext_snoc <;> intro p <;> simp [γ, iVar, jVar]

theorem lift_comp_γ0 (h : Hom n'' n) (g : Hom n' n'') : (Hom.lift h).comp (γ0 g) = γ0 (h.comp g) := by
  apply Hom.ext_snoc <;> intro p <;> simp [γ0]

theorem lift_comp_endpt1 (h : Hom n'' n) :
    (Hom.lift h).comp (Hom.endpt n'' (DM.one n'')) = (Hom.endpt n (DM.one n)).comp h := by
  apply Hom.ext_snoc <;> intro p <;> simp

theorem lift_comp_endpt0 (h : Hom n'' n) :
    (Hom.lift h).comp (Hom.endpt n'' (DM.zero n'')) = (Hom.endpt n (DM.zero n)).comp h := by
  apply Hom.ext_snoc <;> intro p <;> simp

theorem wk_comp_lift' (h : Hom n'' n') : (Hom.wk n').comp (Hom.lift h) = h.comp (Hom.wk n'') :=
  Hom.wk_comp_lift h

/-! ### Faces -/

theorem ψ_endpt0 (φ : Cof n) (g : Hom n' n) : (ψ φ g).restr (Hom.endpt n' (DM.zero _)) = φ.restr g := by
  rw [ψ, Cof.or_restr, Cof.eq1_restr, Cof.restr_restr, Hom.comp_assoc, Hom.wk_comp_endpt, Hom.comp_id]
  have : (DM.var (Fin.last n')).restr (Hom.endpt n' (DM.zero n')) = DM.zero n' := by
    ext p; simp
  rw [this, Cof.eq1_zero, Cof.or_bot]

theorem ψ_endpt1_holds (φ : Cof n) (g : Hom n' n) : ((ψ φ g).restr (Hom.endpt n' (DM.one _))).holds := by
  rw [ψ, Cof.or_restr, Cof.eq1_restr, Cof.holds_or]
  right
  have : (DM.var (Fin.last n')).restr (Hom.endpt n' (DM.one n')) = DM.one n' := by
    ext p; simp
  rw [this, Cof.eq1_one]; exact Cof.holds_top

theorem ψ_lift (φ : Cof n) (g : Hom n' n) (h : Hom n'' n') : (ψ φ g).restr (Hom.lift h) = ψ φ (g.comp h) := by
  rw [ψ, ψ, Cof.or_restr, Cof.eq1_restr, Cof.restr_restr, Hom.comp_assoc, Hom.wk_comp_lift]
  have : (DM.var (Fin.last n')).restr (Hom.lift h) = DM.var (Fin.last n'') := by
    ext p; simp
  rw [this, ← Hom.comp_assoc]

theorem ψ_restr (φ : Cof n) (h : Hom n'' n) (g : Hom n' n'') : ψ (φ.restr h) g = ψ φ (h.comp g) := by
  rw [ψ, ψ, Cof.restr_restr, Hom.comp_assoc]

theorem isCof_ψ {φ : Cof n} (hφ : φ.IsCof) (g : Hom n' n) : (ψ φ g).IsCof :=
  (hφ.restr _).or (Cof.isCof_eq1 _)

end TranspPi

/-! ### General facts about transport -/

theorem transpAt_res (c : V) (f : Hom k m) (g : Hom (n + 1) k) (φ : Cof n) (a0 : V) :
    transpAt (res f c) g φ a0 = transpAt c (f.comp g) φ a0 := by
  simp [transpAt, trG_res]

theorem ConstOn.restr {c : V} {f : Hom (n + 1) m} {φ : Cof n} (hc : ConstOn c f φ) (h : Hom n' n) :
    ConstOn c (f.comp (Hom.lift h)) (φ.restr h) := by
  intro n'' h' hh r
  rw [Cof.restr_restr] at hh
  have e : ∀ x : DM n'', (f.comp (Hom.lift h)).comp (Hom.snoc h' x) = f.comp (Hom.snoc (h.comp h') x) := by
    intro x; rw [Hom.comp_assoc]; congr 1; apply Hom.ext_snoc <;> intro p <;> simp
  rw [e, e]; exact hc n'' (h.comp h') hh r

theorem Fib.transp_base_restr {c : V} (hc : Fib c m) {f : Hom (n + 1) m} {a0 : V}
    (ha : a0 ∈ El c (f.comp (Hom.endpt n (DM.zero n)))) (h : Hom n' n) :
    res h a0 ∈ El c ((f.comp (Hom.lift h)).comp (Hom.endpt n' (DM.zero n'))) := by
  have := hc.elRes _ _ a0 ha n' h
  rw [Hom.comp_assoc, TranspPi.lift_comp_endpt0]; exact this

/-- On the face, a restricted transport is the restricted base. -/
theorem Fib.transp_restr_face {c : V} (hc : Fib c m) {f : Hom (n + 1) m} {φ : Cof n} {a0 : V}
    (hφ : φ.IsCof) (hcon : ConstOn c f φ) (ha : a0 ∈ El c (f.comp (Hom.endpt n (DM.zero n))))
    (h : Hom n' n) (hh : (φ.restr h).holds) : res h (transpAt c f φ a0) = res h a0 := by
  rw [hc.trRes n f φ a0 hφ hcon ha n' h]
  exact hc.trFace n' _ _ _ (hφ.restr h) (hcon.restr h) (hc.transp_base_restr ha h) hh

theorem piC_inj {A1 B1 A2 B2 : V} (hA1 : IsKV k A1) (hB1 : IsKV k B1) (hA2 : IsKV k A2)
    (hB2 : IsKV k B2) (h : piC k A1 B1 = piC k A2 B2) : A1 = A2 ∧ B1 = B2 := by
  have := congrArg (fun c => shapeOf c (Hom.id k)) h
  simp only [piC, shapeOf_mkKV, piDatum, π1_quad, tagZ_inj, pair_inj', true_and] at this
  rwa [res_id hA1, res_id hB1, res_id hA2, res_id hB2] at this

section transp

open TranspPi

variable {A B : V} (hA : Fib A m) (hB : FamOK A B m) {f : Hom (n + 1) m} {φ : Cof n}
  (hφ : φ.IsCof) (hc : ConstOn (piC m A B) f φ)

include hA hB hc in
theorem constAB (h : Hom n' n) (hh : (φ.restr h).holds) (r : DM n') :
    res (f.comp (Hom.snoc h r)) A = res (f.comp (Hom.snoc h (DM.zero n'))) A ∧
    res (f.comp (Hom.snoc h r)) B = res (f.comp (Hom.snoc h (DM.zero n'))) B := by
  have := hc n' h hh r
  rw [res_piC, res_piC] at this
  exact piC_inj (isKV_res _ _) (isKV_res _ _) (isKV_res _ _) (isKV_res _ _) this

theorem w_eq (g : Hom n' n) (v : V) :
    w (res f A) φ g v = transpAt A (f.comp (γ g)) (ψ φ g) (res (Hom.wk n') v) := by
  rw [w, transpAt_res]

theorem w0_eq (g : Hom n' n) (v : V) :
    w0 (res f A) φ g v = transpAt A (f.comp (γ0 g)) (φ.restr g) v := by
  rw [w0, transpAt_res]

include hA hB hc in
theorem constW (g : Hom n' n) : ConstOn A (f.comp (γ g)) (ψ φ g) := by
  intro n'' h hh r
  rw [Hom.comp_assoc, Hom.comp_assoc, γ_comp_snoc, γ_comp_snoc]
  rw [ψ, Cof.or_restr, Cof.holds_or] at hh
  rcases hh with hh | hh
  · rw [Cof.restr_restr] at hh
    rw [(constAB hA hB hc _ hh (DM.max _ (DM.neg r))).1,
      (constAB hA hB hc _ hh (DM.max _ (DM.neg (DM.zero _)))).1]
  · rw [Cof.eq1_restr, Cof.holds_eq1] at hh
    rw [DM.eq_one_of_holds hh, DM.max_one_left, DM.max_one_left]

include hA in
theorem baseW (g : Hom n' n) {v : V} (hv : v ∈ El A (f.comp ((Hom.endpt n (DM.one n)).comp g))) :
    res (Hom.wk n') v ∈ El A ((f.comp (γ g)).comp (Hom.endpt (n' + 1) (DM.zero _))) := by
  rw [Hom.comp_assoc, γ_endpt0]; exact hA.elRes _ _ v hv _ (Hom.wk n')

include hA hB hc hφ in
theorem memW (g : Hom n' n) {v : V} (hv : v ∈ El A (f.comp ((Hom.endpt n (DM.one n)).comp g))) :
    w (res f A) φ g v ∈ El A (f.comp (Hom.lift g)) := by
  have := hA.trMem (n' + 1) (f.comp (γ g)) (ψ φ g) _ (isCof_ψ hφ g) (constW hA hB hc g) (baseW hA g hv)
  rwa [Hom.comp_assoc, γ_endpt1, ← w_eq] at this

include hA hB hc in
theorem constW0 (g : Hom n' n) : ConstOn A (f.comp (γ0 g)) (φ.restr g) := by
  intro n'' h hh r
  rw [Hom.comp_assoc, Hom.comp_assoc, γ0_comp_snoc, γ0_comp_snoc]
  rw [Cof.restr_restr] at hh
  rw [(constAB hA hB hc _ hh (DM.neg r)).1, (constAB hA hB hc _ hh (DM.neg (DM.zero _))).1]

include hA hB hc hφ in
theorem memW0 (g : Hom n' n) {v : V} (hv : v ∈ El A (f.comp ((Hom.endpt n (DM.one n)).comp g))) :
    w0 (res f A) φ g v ∈ El A (f.comp ((Hom.endpt n (DM.zero n)).comp g)) := by
  have := hA.trMem n' (f.comp (γ0 g)) (φ.restr g) v (hφ.restr g) (constW0 hA hB hc g)
    (by rw [Hom.comp_assoc, γ0_endpt0]; exact hv)
  rwa [Hom.comp_assoc, γ0_endpt1, ← w0_eq] at this

include hA hB hc hφ in
theorem w_endpt0 (g : Hom n' n) {v : V} (hv : v ∈ El A (f.comp ((Hom.endpt n (DM.one n)).comp g))) :
    res (Hom.endpt n' (DM.zero n')) (w (res f A) φ g v) = w0 (res f A) φ g v := by
  rw [w_eq, hA.trRes (n' + 1) _ _ _ (isCof_ψ hφ g) (constW hA hB hc g) (baseW hA g hv) n'
    (Hom.endpt n' (DM.zero n')), Hom.comp_assoc, γ_lift_endpt0, ψ_endpt0, res_res,
    Hom.wk_comp_endpt, res_id (hA.elKV _ _ v hv), w0_eq]

include hA hB hc hφ in
theorem w_endpt1 (g : Hom n' n) {v : V} (hv : v ∈ El A (f.comp ((Hom.endpt n (DM.one n)).comp g))) :
    res (Hom.endpt n' (DM.one n')) (w (res f A) φ g v) = v := by
  rw [w_eq, hA.transp_restr_face (isCof_ψ hφ g) (constW hA hB hc g) (baseW hA g hv) _
    (ψ_endpt1_holds φ g), res_res, Hom.wk_comp_endpt, res_id (hA.elKV _ _ v hv)]

include hA hB hc hφ in
theorem w_const (g : Hom n' n) {v : V} (hv : v ∈ El A (f.comp ((Hom.endpt n (DM.one n)).comp g)))
    (h : Hom n'' n') (hh : (φ.restr (g.comp h)).holds) (r : DM n'') :
    res (Hom.snoc h r) (w (res f A) φ g v) = res h v := by
  have hh' : ((ψ φ g).restr (Hom.snoc h r)).holds := by
    rw [ψ, Cof.or_restr, Cof.holds_or]; left
    rw [Cof.restr_restr, Hom.comp_assoc, Hom.wk_comp_snoc]; exact hh
  rw [w_eq, hA.transp_restr_face (isCof_ψ hφ g) (constW hA hB hc g) (baseW hA g hv) _ hh', res_res,
    Hom.wk_comp_snoc]

theorem lift_comp_snoc (g : Hom n' n) (h : Hom n'' n') (r : DM n'') :
    (Hom.lift g).comp (Hom.snoc h r) = Hom.snoc (g.comp h) r := by
  apply Hom.ext_snoc <;> intro p <;> simp

theorem snoc_zero_eq (g : Hom n' n) : Hom.snoc g (DM.zero n') = (Hom.endpt n (DM.zero n)).comp g := by
  apply Hom.ext_snoc <;> intro p <;> simp

theorem snoc_one_eq (g : Hom n' n) : Hom.snoc g (DM.one n') = (Hom.endpt n (DM.one n)).comp g := by
  apply Hom.ext_snoc <;> intro p <;> simp

theorem C_eq (g : Hom n' n) (v : V) :
    C (res f A) (res f B) φ g v = apZ (dat B (n' + 1) (f.comp (Hom.lift g))) (w (res f A) φ g v) := by
  rw [C, dat_res]

include hA hB hc hφ in
theorem fibC (g : Hom n' n) {v : V} (hv : v ∈ El A (f.comp ((Hom.endpt n (DM.one n)).comp g))) :
    Fib (C (res f A) (res f B) φ g v) (n' + 1) := by
  rw [C_eq]; exact hB.fib _ _ _ (memW hA hB hφ hc g hv)

include hA hB hc hφ in
theorem resC (g : Hom n' n) {v : V} (hv : v ∈ El A (f.comp ((Hom.endpt n (DM.one n)).comp g)))
    (x : Hom n'' (n' + 1)) :
    res x (C (res f A) (res f B) φ g v) =
      apZ (dat B n'' ((f.comp (Hom.lift g)).comp x)) (res x (w (res f A) φ g v)) := by
  rw [C_eq]; exact hB.coh _ _ _ (memW hA hB hφ hc g hv) _ x

include hA hB hc hφ in
theorem constC (g : Hom n' n) {v : V} (hv : v ∈ El A (f.comp ((Hom.endpt n (DM.one n)).comp g))) :
    ConstOn (C (res f A) (res f B) φ g v) (Hom.id (n' + 1)) (φ.restr g) := by
  intro n'' h hh r
  rw [Hom.id_comp, Hom.id_comp, resC hA hB hφ hc g hv, resC hA hB hφ hc g hv]
  rw [Cof.restr_restr] at hh
  rw [w_const hA hB hφ hc g hv h hh r, w_const hA hB hφ hc g hv h hh (DM.zero _),
    Hom.comp_assoc, Hom.comp_assoc, lift_comp_snoc, lift_comp_snoc]
  have := congrArg (fun X => dat X n'' (Hom.id n'')) (constAB hA hB hc (g.comp h) hh r).2
  simp only [dat_res, Hom.comp_id] at this
  rw [this]

include hA hB hc hφ in
theorem baseC (g : Hom n' n) {v : V} (hv : v ∈ El A (f.comp ((Hom.endpt n (DM.one n)).comp g)))
    {u0 : V} (hu0 : u0 ∈ El (piC m A B) (f.comp (Hom.endpt n (DM.zero n)))) :
    appV n' (res g u0) (w0 (res f A) φ g v) ∈
      El (C (res f A) (res f B) φ g v) ((Hom.id (n' + 1)).comp (Hom.endpt n' (DM.zero n'))) := by
  rw [Hom.id_comp, ← Hom.comp_id (Hom.endpt n' (DM.zero n')), ← El_res, resC hA hB hφ hc g hv,
    w_endpt0 hA hB hφ hc g hv, Hom.comp_assoc, Hom.lift_comp_endpt', snoc_zero_eq]
  rw [El_piC] at hu0
  have h1 := res_mem_piElSet hu0 g
  rw [res_res, res_res] at h1
  have h2 : w0 (res f A) φ g v ∈ El (res ((f.comp (Hom.endpt n (DM.zero n))).comp g) A) (Hom.id n') := by
    rw [El_res, Hom.comp_id]; exact memW0 hA hB hφ hc g hv
  have := appV_mem_piElSet h1 h2
  rwa [dat_res, Hom.comp_id] at this

include hA hB hc hφ in
theorem memC (g : Hom n' n) {v : V} (hv : v ∈ El A (f.comp ((Hom.endpt n (DM.one n)).comp g)))
    {u0 : V} (hu0 : u0 ∈ El (piC m A B) (f.comp (Hom.endpt n (DM.zero n)))) :
    transpAt (C (res f A) (res f B) φ g v) (Hom.id (n' + 1)) (φ.restr g)
        (appV n' (res g u0) (w0 (res f A) φ g v)) ∈
      El (apZ (dat B n' (f.comp ((Hom.endpt n (DM.one n)).comp g))) v) (Hom.id n') := by
  have := (fibC hA hB hφ hc g hv).trMem n' (Hom.id _) (φ.restr g) _ (hφ.restr g)
    (constC hA hB hφ hc g hv) (baseC hA hB hφ hc g hv hu0)
  rwa [Hom.id_comp, ← Hom.comp_id (Hom.endpt n' (DM.one n')), ← El_res, resC hA hB hφ hc g hv,
    w_endpt1 hA hB hφ hc g hv, Hom.comp_assoc, Hom.lift_comp_endpt', snoc_one_eq] at this

theorem transpPiF_eq (A' B' : V) (u0 : V) :
    transpPiF n A' B' φ u0 = lamV n (fun _ g => El A' ((Hom.endpt n (DM.one n)).comp g))
      (fun n' g v => transpAt (C A' B' φ g v) (Hom.id (n' + 1)) (φ.restr g)
        (appV n' (res g u0) (w0 A' φ g v))) := rfl

theorem piElSet_line_eq (f : Hom (n + 1) m) (r : DM n) :
    piElSet n (res (f.comp (Hom.endpt n r)) A) (res (f.comp (Hom.endpt n r)) B) =
      piEl n (fun _ g => El (res f A) ((Hom.endpt n r).comp g))
        (fun n' g a => El (apZ (dat B n' (f.comp ((Hom.endpt n r).comp g))) a) (Hom.id n')) := by
  unfold piElSet; simp only [El_res, dat_res]; rfl

include hA hB hc hφ in
theorem transpPiF_mem {u0 : V} (hu0 : u0 ∈ El (piC m A B) (f.comp (Hom.endpt n (DM.zero n)))) :
    transpPiF n (res f A) (res f B) φ u0 ∈
      piElSet n (res (f.comp (Hom.endpt n (DM.one n))) A) (res (f.comp (Hom.endpt n (DM.one n))) B) := by
  rw [piElSet_line_eq, transpPiF_eq]
  apply lamV_mem_piEl
  · intro n' g a ha n'' h
    rw [El_res] at ha ⊢; exact hA.elRes _ _ a ha n'' h
  · intro n' g v hv
    rw [El_res] at hv
    exact memC hA hB hφ hc g hv hu0
  · intro n' g v hv n'' h
    rw [El_res] at hv
    have hfib := fibC hA hB hφ hc g hv
    rw [hfib.trRes n' (Hom.id _) (φ.restr g) _ (hφ.restr g) (constC hA hB hφ hc g hv)
      (baseC hA hB hφ hc g hv hu0) n'' h, Hom.id_comp, transpAt_eq_res_id, Cof.restr_restr]
    have hv' : res h v ∈ El A (f.comp ((Hom.endpt n (DM.one n)).comp (g.comp h))) :=
      hA.elRes _ _ v hv n'' h
    congr 1
    · -- the codomain line
      rw [resC hA hB hφ hc g hv, C_eq, Hom.comp_assoc, Hom.lift_comp, w_eq, w_eq,
        hA.trRes (n' + 1) _ _ _ (isCof_ψ hφ g) (constW hA hB hc g) (baseW hA g hv) (n'' + 1) (Hom.lift h),
        Hom.comp_assoc, γ_comp_lift_lift, ψ_lift, res_res, res_res, wk_comp_lift']
    · -- the base
      rw [El_piC] at hu0
      have h1 := res_mem_piElSet hu0 g
      rw [res_res, res_res] at h1
      have h2 : w0 (res f A) φ g v ∈ El (res ((f.comp (Hom.endpt n (DM.zero n))).comp g) A) (Hom.id n') := by
        rw [El_res, Hom.comp_id]; exact memW0 hA hB hφ hc g hv
      rw [res_appV h1 h2 h, res_res, w0_eq, w0_eq,
        hA.trRes n' _ _ v (hφ.restr g) (constW0 hA hB hc g) (by rw [Hom.comp_assoc, γ0_endpt0]; exact hv) n'' h,
        Hom.comp_assoc, γ0_comp_lift, Cof.restr_restr]

include hA hB hc hφ in
theorem transpPiF_face {u0 : V} (hu0 : u0 ∈ El (piC m A B) (f.comp (Hom.endpt n (DM.zero n))))
    (hh : φ.holds) : transpPiF n (res f A) (res f B) φ u0 = u0 := by
  have hid : (φ.restr (Hom.id n)).holds := by rw [hφ.restr_id]; exact hh
  have hAB := constAB hA hB hc (Hom.id n) hid (DM.one n)
  have hmem := transpPiF_mem hA hB hφ hc hu0
  rw [El_piC] at hu0
  have e1 : Hom.snoc (Hom.id n) (DM.one n) = Hom.endpt n (DM.one n) := rfl
  have e0 : Hom.snoc (Hom.id n) (DM.zero n) = Hom.endpt n (DM.zero n) := rfl
  rw [e1, e0] at hAB
  rw [hAB.1, hAB.2] at hmem
  refine piEl_ext (D := fun _ g => El (res (f.comp (Hom.endpt n (DM.zero n))) A) g) hmem hu0
    fun n' g v hv => ?_
  have hv1 : v ∈ El A (f.comp ((Hom.endpt n (DM.one n)).comp g)) := by
    have : v ∈ El (res (f.comp (Hom.endpt n (DM.zero n))) A) g := hv
    rwa [← hAB.1, El_res] at this
  have hg : (φ.restr g).holds := hφ.holds_restr hh g
  rw [apZ_dat_transpPiF _ _ _ _ _ (by rw [El_res]; exact hv1),
    (fibC hA hB hφ hc g hv1).trFace n' (Hom.id _) (φ.restr g) _ (hφ.restr g)
      (constC hA hB hφ hc g hv1) (baseC hA hB hφ hc g hv1 (by rwa [El_piC])) hg,
    w0_eq, hA.trFace n' _ _ v (hφ.restr g) (constW0 hA hB hc g)
      (by rw [Hom.comp_assoc, γ0_endpt0]; exact hv1) hg, appV_res]

end transp

theorem transpPiF_res {A B : V} (f : Hom (n + 1) m) (φ : Cof n) (u0 : V) (h : Hom n'' n) :
    res h (transpPiF n (res f A) (res f B) φ u0) =
      transpPiF n'' (res (f.comp (Hom.lift h)) A) (res (f.comp (Hom.lift h)) B) (φ.restr h) (res h u0) := by
  rw [transpPiF_eq, transpPiF_eq, res_lamV]
  congr 1
  · funext n' g
    rw [El_res, El_res, Hom.comp_assoc, ← Hom.comp_assoc (Hom.lift h), TranspPi.lift_comp_endpt1]; rfl
  · funext n' g v
    simp only [TranspPi.C, TranspPi.w, TranspPi.w0, dat_res, transpAt_res, Hom.comp_assoc,
      Hom.lift_comp, TranspPi.lift_comp_γ, TranspPi.lift_comp_γ0, TranspPi.ψ_restr, Cof.restr_restr,
      res_res]

theorem transpAt_piC {A B : V} {f : Hom (n + 1) m} {φ : Cof n} {u0 : V}
    (hu0 : u0 ∈ El (piC m A B) (f.comp (Hom.endpt n (DM.zero n)))) :
    transpAt (piC m A B) f φ u0 = transpPiF n (res f A) (res f B) φ u0 := by
  rw [transpAt, trG_piC]
  show apZ (trGraph n _ _) _ = _
  rw [apZ_trGraph]
  rw [El_piC] at hu0; rwa [res_res, res_res]

/-- **Π-types are fibrant**, with the spec's `hcompPi` and `transpPi`. -/
theorem fib_piC {A B : V} (hA : Fib A m) (hB : FamOK A B m) : Fib (piC m A B) m where
  kv := isKV_mkKV _
  elKV k f v hv := by rw [El_piC, piElSet, mem_piEl] at hv; exact hv.1
  elRes k f v hv n h := by
    rw [El_piC] at hv ⊢; have := res_mem_piElSet hv h; rwa [res_res, res_res] at this
  hcMem k f φ u u0 hφ hu0 hu := by
    rw [hcompAt_piC hA hB hu0 hu, El_piC]; exact hcompPiF_mem hA hB hφ hu0 hu
  hcFace k f φ u u0 hφ hu0 hu hh := by
    rw [hcompAt_piC hA hB hu0 hu]; exact hcompPiF_face hA hB hφ hu0 hu hh
  hcRes k f φ u u0 hφ hu0 hu n h := by
    have hu0' : res h u0 ∈ El (piC m A B) (f.comp h) := by
      rw [El_piC] at hu0 ⊢; have := res_mem_piElSet hu0 h; rwa [res_res, res_res] at this
    rw [hcompAt_piC hA hB hu0 hu, hcompAt_piC hA hB hu0' (hu.restr h), hcompPiF_res, res_res,
      res_res, Tube.canon_restr]
  trMem n f φ a0 hφ hc ha := by
    rw [transpAt_piC ha, El_piC]; exact transpPiF_mem hA hB hφ hc ha
  trFace n f φ a0 hφ hc ha hh := by
    rw [transpAt_piC ha]; exact transpPiF_face hA hB hφ hc ha hh
  trRes n f φ a0 hφ hc ha n' h := by
    have ha' : res h a0 ∈ El (piC m A B) ((f.comp (Hom.lift h)).comp (Hom.endpt n' (DM.zero n'))) := by
      rw [El_piC] at ha ⊢; have := res_mem_piElSet ha h
      rw [Hom.comp_assoc f (Hom.lift h), TranspPi.lift_comp_endpt0, ← Hom.comp_assoc]
      rwa [res_res, res_res] at this
    rw [transpAt_piC ha, transpAt_piC ha', transpPiF_res]

end

end Model
