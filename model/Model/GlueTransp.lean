import Model.GlueFib
import Model.EquivCode
import Model.CofForall
import Model.CompFill

/-!
# Transport in Glue types

The model's transport along a line of Glue types `i ↦ Glue A(i) [φ(i) ↦ (T(i), e(i))]` (at stage
`n + 1`, `i` the last variable) is the semantic reading of the spec's `Tm.transpGlue` (after
Coquand–Huber–Mörtberg):

* `a0 = unglue φ(0) e(0) u0`, and the tube `i ↦ unglue φ(i) e(i) u0` on `ψ`;
* `a1' = comp (i. A) [ψ ↦ unglue u0] a0`;
* on `δ = ∀ i. φ`: `t1' = transp (i. T) ψ u0` and a path `ω` in `A(1)` from `e(1).1 t1'` to `a1'`;
* on `φ(1)`: `ext`, the extension of the partial element `[δ ↦ (t1', ω), ψ ↦ (u0, refl)]` of the
  fiber of `e(1).1` over `a1'`, by contractibility (`hcomp` in the fiber from the center);
* `a1 = hcomp A(1) [φ(1) ↦ (snd ext)(~j), ψ ↦ a1'] a1'`, and the result `glue [φ(1) ↦ fst ext] a1`.
-/

set_option autoImplicit false

namespace Model

open ZFSet KubusCore

noncomputable section

attribute [local instance] Classical.propDecidable

variable {k k' m n n' : ℕ}


/-! ### The ingredients of Glue transport -/

section gt

variable {A : V} {φ : Cof (n + 1)} {Tp ep : V} (hG : GlueOK A φ Tp ep) {ψ : Cof n} (hψ : ψ.IsCof)
  {u0 : V} (hu0 : u0 ∈ El (glueC (n + 1) A φ Tp ep) (eZ n))
  (hcon : ConstOn (glueC (n + 1) A φ Tp ep) (Hom.id (n + 1)) ψ)

include hG hu0 hcon in
/-- On `ψ`, `u0` lies in the Glue type at every point of the line. -/
theorem gt_u_mem {g : Hom k n} (hg : (ψ.restr g).holds) (r : DM k) :
    res g u0 ∈ El (glueC (n + 1) A φ Tp ep) (Hom.snoc g r) := by
  have h0 := hG.elRes hu0 g
  rw [← snoc_zero_eq, El_eq_res_id] at h0
  rw [El_eq_res_id]
  have := hcon k g hg r
  rw [Hom.id_comp, Hom.id_comp] at this
  rwa [this]

include hG hu0 in
theorem gt_A0_mem : gtA0 φ ep u0 ∈ El A ((Hom.id (n + 1)).comp (eZ n)) := by
  rw [Hom.id_comp]; exact hG.ung_mem hu0

include hG hu0 hcon in
theorem gt_tube_ok : LineTubeOK A (Hom.id (n + 1)) ψ (gtTube φ ep u0) (gtA0 φ ep u0) where
  mem k g r hg := by rw [Hom.id_comp]; exact hG.ung_mem (gt_u_mem hG hu0 hcon hg r)
  coh k g r hg k' h := by
    simp only [gtTube]
    rw [hG.ung_res (gt_u_mem hG hu0 hcon hg r) h, Hom.snoc_comp, res_res]
  base k g hg := by
    simp only [gtTube, gtA0]
    rw [hG.ung_res hu0 g, snoc_zero_eq]

include hG hψ hu0 hcon in
theorem gt_A1'_mem : gtA1' A φ ep ψ u0 ∈ El A ((Hom.id (n + 1)).comp (eO n)) :=
  compF_mem hG.fibA hψ (gt_A0_mem hG hu0) (gt_tube_ok hG hu0 hcon)

include hG hψ hu0 hcon in
theorem gt_A1'_face (hh : ψ.holds) :
    gtA1' A φ ep ψ u0 = ungAt n (φ.restr (eO n)) (dat ep n (eO n)) u0 := by
  rw [gtA1', compF_face hG.fibA hψ (gt_A0_mem hG hu0) (gt_tube_ok hG hu0 hcon) hh]
  simp only [gtTube]
  rw [res_id (hG.elKV hu0)]
  rfl

end gt

/-! ### `δ = ∀ i. φ` -/

theorem gt_δ_lift {φ : Cof (n + 1)} (g : Hom k n) :
    ((gtδ φ).restr g).holds ↔ (φ.restr (Hom.lift g)).holds := by
  simp only [gtδ, Cof.forall0, Cof.restr, Cof.holds, Set.mem_setOf_eq, Hom.app_lift]
  constructor
  · rintro ⟨-, -, hq⟩; refine ⟨Pt.allA_isK3 _, ?_⟩; simpa [Fin.init, Pt.allA] using hq
  · rintro ⟨-, hq⟩
    refine ⟨Pt.allA_isK3 _, Hom.app_isK3 g (Pt.allA_isK3 k), ?_⟩
    simpa [Fin.init, Pt.allA] using hq

theorem gt_δ_snoc {φ : Cof (n + 1)} (hφ : φ.IsCof) {g : Hom k n} (hg : ((gtδ φ).restr g).holds) (r : DM k) :
    (φ.restr (Hom.snoc g r)).holds :=
  Cof.forall0_holds_snoc hφ hg r

theorem gt_δ_cof {φ : Cof (n + 1)} (hφ : φ.IsCof) : (gtδ φ).IsCof := Cof.IsCof.forall0 hφ

/-! ### The `T`-part, on `δ` -/

section gtT

variable {A : V} {φ : Cof (n + 1)} {Tp ep : V} (hG : GlueOK A φ Tp ep) {ψ : Cof n} (hψ : ψ.IsCof)
  {u0 : V} (hu0 : u0 ∈ El (glueC (n + 1) A φ Tp ep) (eZ n))
  (hcon : ConstOn (glueC (n + 1) A φ Tp ep) (Hom.id (n + 1)) ψ)

include hG in
theorem gt_TL_fib {g : Hom k n} (hg : ((gtδ φ).restr g).holds) : Fib (gtTL Tp g) (k + 1) :=
  hG.fibT (k + 1) (Hom.lift g) ((gt_δ_lift g).1 hg)

include hG in
theorem gt_TL_res {g : Hom k n} (hg : ((gtδ φ).restr g).holds) (h : Hom k' (k + 1)) :
    res h (gtTL Tp g) = dat Tp k' ((Hom.lift g).comp h) :=
  hG.Tcoh (k + 1) (Hom.lift g) ((gt_δ_lift g).1 hg) k' h

include hG in
/-- On `δ` the Glue type at a point of the line is `T` there. -/
theorem gt_glue_T {g : Hom k n} (hg : ((gtδ φ).restr g).holds) (r : DM k) :
    res (Hom.snoc g r) (glueC (n + 1) A φ Tp ep) = dat Tp k (Hom.snoc g r) := by
  rw [res_glueC hG.Tcoh (fun k f hf => (hG.fibT k f hf).kv) hG.cof, if_pos (gt_δ_snoc hG.cof hg r)]

include hG hcon in
theorem gt_TL_const {g : Hom k n} (hg : ((gtδ φ).restr g).holds) :
    ConstOn (gtTL Tp g) (Hom.id (k + 1)) (ψ.restr g) := by
  intro k' h hh r
  rw [Cof.restr_restr] at hh
  have hgh : ((gtδ φ).restr (g.comp h)).holds := by
    rw [← Cof.restr_restr]; exact ((gt_δ_cof hG.cof).restr g).holds_restr hg h
  rw [Hom.id_comp, Hom.id_comp, gt_TL_res hG hg, gt_TL_res hG hg, lift_comp_snoc, lift_comp_snoc,
    ← gt_glue_T hG hgh, ← gt_glue_T hG hgh]
  have := hcon k' (g.comp h) hh r
  rwa [Hom.id_comp, Hom.id_comp] at this

include hG hu0 in
theorem gt_u0_TL {g : Hom k n} (hg : ((gtδ φ).restr g).holds) :
    res g u0 ∈ El (gtTL Tp g) ((Hom.id (k + 1)).comp (eZ k)) := by
  have h0 := hG.elRes hu0 g
  rw [← snoc_zero_eq, El_eq_res_id, gt_glue_T hG hg] at h0
  rw [Hom.id_comp, El_eq_res_id, gt_TL_res hG hg, TranspPi.lift_comp_endpt0, ← snoc_zero_eq]
  exact h0

include hG hψ hu0 hcon in
theorem gt_T1'_mem {g : Hom k n} (hg : ((gtδ φ).restr g).holds) :
    gtT1' Tp ψ u0 g ∈ El (gtT1 Tp g) (Hom.id k) := by
  have := (gt_TL_fib hG hg).trMem k _ _ _ (hψ.restr g) (gt_TL_const hG hcon hg) (gt_u0_TL hG hu0 hg)
  rw [Hom.id_comp, El_eq_res_id, gt_TL_res hG hg, TranspPi.lift_comp_endpt1] at this
  unfold gtT1; rw [← snoc_one_eq] at this ⊢
  rw [snoc_one_eq]; rw [snoc_one_eq] at this; exact this

end gtT

/-! ### The path `ω` -/

theorem gtΩLine_snoc (g : Hom k n) (h : Hom n' (k + 1)) (r : DM n') :
    (gtΩLine g).comp (Hom.snoc h r) = Hom.snoc ((g.comp (Hom.wk k)).comp h) r := by
  apply Hom.ext_snoc
  · intro p; apply funext; intro j; simp [gtΩLine]
  · intro p; simp [gtΩLine]

section gtΩ

variable {A : V} {φ : Cof (n + 1)} {Tp ep : V} (hG : GlueOK A φ Tp ep) {ψ : Cof n} (hψ : ψ.IsCof)
  {u0 : V} (hu0 : u0 ∈ El (glueC (n + 1) A φ Tp ep) (eZ n))
  (hcon : ConstOn (glueC (n + 1) A φ Tp ep) (Hom.id (n + 1)) ψ)

include hG in
theorem gt_e_mem {P : Hom n' (n + 1)} (hP : (φ.restr P).holds) {x : V} (hx : x ∈ El (dat Tp n' P) (Hom.id n')) :
    eqFun n' (dat ep n' P) x ∈ El A P := by
  have := eqFun_mem (hG.fibT n' P hP).kv (isKV_res P A) (hG.mem_e n' P hP) hx
  rwa [El_res, Hom.comp_id] at this

include hG in
theorem gt_e_res {P : Hom n' (n + 1)} (hP : (φ.restr P).holds) {x : V} (hx : x ∈ El (dat Tp n' P) (Hom.id n'))
    (h : Hom k n') : res h (eqFun n' (dat ep n' P) x) = eqFun k (dat ep k (P.comp h)) (res h x) := by
  rw [eqFun_res' (hG.fibT n' P hP).kv (hG.mem_e n' P hP) hx h, hG.ecoh n' P hP k h]

include hG hu0 in
/-- `u0` lies in `T(0)` on `δ`. -/
theorem gt_u0_T0 {g : Hom k n} (hg : ((gtδ φ).restr g).holds) :
    res g u0 ∈ El (dat Tp k (Hom.snoc g (DM.zero k))) (Hom.id k) := by
  have h0 := hG.elRes hu0 g
  rwa [← snoc_zero_eq, El_eq_res_id, gt_glue_T hG hg] at h0

include hG hu0 hcon in
/-- On `ψ ∧ δ`, `u0` lies in `T` at every point of the line. -/
theorem gt_u0_T {g : Hom k n} (hg : ((gtδ φ).restr g).holds) (hψg : (ψ.restr g).holds) (r : DM k) :
    res g u0 ∈ El (dat Tp k (Hom.snoc g r)) (Hom.id k) := by
  have h0 := gt_u_mem hG hu0 hcon hψg r
  rwa [El_eq_res_id, gt_glue_T hG hg] at h0

end gtΩ

section gtΩ2

variable {A : V} {φ : Cof (n + 1)} {Tp ep : V} (hG : GlueOK A φ Tp ep) {ψ : Cof n} (hψ : ψ.IsCof)
  {u0 : V} (hu0 : u0 ∈ El (glueC (n + 1) A φ Tp ep) (eZ n))
  (hcon : ConstOn (glueC (n + 1) A φ Tp ep) (Hom.id (n + 1)) ψ)

include hG hψ hu0 hcon in
/-- The transport filler of `u0` in `T`, above `g`. -/
theorem gt_tfill {g : Hom k n} (hg : ((gtδ φ).restr g).holds) :
    let tf := transpFillF (gtTL Tp g) (Hom.id (k + 1)) (ψ.restr g) (res g u0)
    tf ∈ El (gtTL Tp g) (Hom.id (k + 1)) ∧
    res (eZ k) tf = res g u0 ∧
    (∀ {n'} (h : Hom n' k), ((ψ.restr g).restr h).holds → ∀ r, res (Hom.snoc h r) tf = res h (res g u0)) := by
  have hfib := gt_TL_fib hG hg
  have hc := gt_TL_const hG hcon hg
  have hb := gt_u0_TL hG hu0 hg
  exact ⟨transpFillF_mem hfib (hψ.restr g) hc hb, transpFillF_endpt0 hfib (hψ.restr g) hc hb,
    fun h hh r => transpFillF_face hfib (hψ.restr g) hc hb h hh r⟩

include hG hψ hu0 hcon in
/-- The filler of the unglued tube in `A`. -/
theorem gt_fillA :
    gtFillA A φ ep ψ u0 ∈ El A (Hom.id (n + 1)) ∧
    res (eZ n) (gtFillA A φ ep ψ u0) = gtA0 φ ep u0 ∧
    res (eO n) (gtFillA A φ ep ψ u0) = gtA1' A φ ep ψ u0 ∧
    (∀ {n'} (h : Hom n' n), (ψ.restr h).holds → ∀ r, res (Hom.snoc h r) (gtFillA A φ ep ψ u0) = gtTube φ ep u0 n' h r) := by
  have hb := gt_A0_mem hG hu0
  have ht := gt_tube_ok hG hu0 hcon
  exact ⟨fillF_mem hG.fibA hψ hb ht, fillF_endpt0 hG.fibA hψ hb ht, fillF_endpt1 hG.fibA hψ hb ht,
    fun h hh r => fillF_face hG.fibA hψ hb ht h hh r⟩

end gtΩ2

section gtΩ3

variable {A : V} {φ : Cof (n + 1)} {Tp ep : V} (hG : GlueOK A φ Tp ep) {ψ : Cof n} (hψ : ψ.IsCof)
  {u0 : V} (hu0 : u0 ∈ El (glueC (n + 1) A φ Tp ep) (eZ n))
  (hcon : ConstOn (glueC (n + 1) A φ Tp ep) (Hom.id (n + 1)) ψ)

include hG in
theorem gt_δ_comp {g : Hom k n} (hg : ((gtδ φ).restr g).holds) (h : Hom n' k) :
    ((gtδ φ).restr (g.comp h)).holds := by
  rw [← Cof.restr_restr]; exact ((gt_δ_cof hG.cof).restr g).holds_restr hg h

include hG hu0 in
theorem gt_ΩBase_mem {g : Hom k n} (hg : ((gtδ φ).restr g).holds) :
    gtΩBase ep u0 g ∈ El A ((gtΩLine g).comp (Hom.endpt (k + 1) (DM.zero (k + 1)))) := by
  have hgw := gt_δ_comp hG hg (Hom.wk k)
  rw [show Hom.endpt (k + 1) (DM.zero (k + 1)) = Hom.snoc (Hom.id (k + 1)) (DM.zero (k + 1)) from rfl,
    gtΩLine_snoc, Hom.comp_id]
  exact gt_e_mem hG (gt_δ_snoc hG.cof hgw _) (gt_u0_T0 hG hu0 hgw)

include hG hψ hu0 hcon in
theorem gt_Ω_ok {g : Hom k n} (hg : ((gtδ φ).restr g).holds) :
    LineTubeOK A (gtΩLine g) (pathFace (ψ.restr g)) (gtΩTube A φ Tp ep ψ u0 g) (gtΩBase ep u0 g) where
  mem n' h r hh := by
    have hb := gt_δ_comp hG hg ((Hom.wk k).comp h)
    rw [← Hom.comp_assoc] at hb
    have hP := gt_δ_snoc hG.cof hb r
    obtain ⟨htf, -, -⟩ := gt_tfill hG hψ hu0 hcon hg
    rw [gtΩLine_snoc]
    unfold gtΩTube
    split_ifs with h1 h2
    · exact gt_e_mem hG hP (gt_u0_T hG hu0 hcon hb h1 r)
    · apply gt_e_mem hG hP
      have := (gt_TL_fib hG hg).elRes _ _ _ htf n' (Hom.snoc ((Hom.wk k).comp h) r)
      rwa [Hom.id_comp, El_eq_res_id, gt_TL_res hG hg, lift_comp_snoc] at this
    · have := hG.fibA.elRes _ _ _ (gt_fillA hG hψ hu0 hcon).1 n' (Hom.snoc ((g.comp (Hom.wk k)).comp h) r)
      rwa [Hom.id_comp] at this
  coh n' h r hh n'' g' := by
    set b := (g.comp (Hom.wk k)).comp h with hbdef
    have hb : ((gtδ φ).restr b).holds := by
      rw [hbdef, Hom.comp_assoc]; exact gt_δ_comp hG hg ((Hom.wk k).comp h)
    have hbg : ((gtδ φ).restr (b.comp g')).holds := gt_δ_comp hG hb g'
    have hP := gt_δ_snoc hG.cof hb r
    obtain ⟨htf, -, htfF⟩ := gt_tfill hG hψ hu0 hcon hg
    obtain ⟨-, -, -, hfF⟩ := gt_fillA hG hψ hu0 hcon
    have hbc : (g.comp (Hom.wk k)).comp (h.comp g') = b.comp g' := rfl
    unfold gtΩTube
    rw [hbc, ← hbdef]
    by_cases h1 : (ψ.restr b).holds
    · have h1' : (ψ.restr (b.comp g')).holds := by
        rw [← Cof.restr_restr]; exact (hψ.restr _).holds_restr h1 g'
      rw [if_pos h1, if_pos h1', gt_e_res hG hP (gt_u0_T hG hu0 hcon hb h1 r), Hom.snoc_comp, res_res]
    · rw [if_neg h1]
      by_cases h2 : ((Cof.eq0 (lastVar k)).restr h).holds
      · have h2' : ((Cof.eq0 (lastVar k)).restr (h.comp g')).holds := by
          rw [← Cof.restr_restr]; exact ((Cof.isCof_eq0 _).restr h).holds_restr h2 g'
        have hx : res (Hom.snoc ((Hom.wk k).comp h) r) (transpFillF (gtTL Tp g) (Hom.id (k + 1)) (ψ.restr g) (res g u0))
            ∈ El (dat Tp n' (Hom.snoc b r)) (Hom.id n') := by
          have := (gt_TL_fib hG hg).elRes _ _ _ htf n' (Hom.snoc ((Hom.wk k).comp h) r)
          rwa [Hom.id_comp, El_eq_res_id, gt_TL_res hG hg, lift_comp_snoc] at this
        rw [if_pos h2, gt_e_res hG hP hx, Hom.snoc_comp, res_res, Hom.snoc_comp]
        by_cases h3 : (ψ.restr (b.comp g')).holds
        · rw [if_pos h3]
          have h3' : ((ψ.restr g).restr ((Hom.wk k).comp (h.comp g'))).holds := by
            rw [Cof.restr_restr]; exact h3
          rw [show ((Hom.wk k).comp h).comp g' = (Hom.wk k).comp (h.comp g') from rfl,
            htfF _ h3' (r.restr g'), res_res]
          rfl
        · rw [if_neg h3, if_pos h2']
          rfl
      · have h1' : (lastVar k).restr h = DM.one n' := by
          rcases pathFace_cases hh with h3 | h3 | h3
          · exact absurd (by rw [Cof.restr_restr, ← Hom.comp_assoc] at h3; exact h3) h1
          · exact absurd (eq0_restr_holds_iff.2 h3) h2
          · exact h3
        have hno : ¬ ((Cof.eq0 (lastVar k)).restr (h.comp g')).holds := by
          rw [eq0_restr_holds_iff, ← DM.restr_restr, h1', DM.one_restr]; exact DM.zero_ne_one'.symm
        rw [if_neg h2, res_res, Hom.snoc_comp]
        by_cases h3 : (ψ.restr (b.comp g')).holds
        · rw [if_pos h3, hfF _ h3]
          have hP' := gt_δ_snoc hG.cof hbg (r.restr g')
          have hm := gt_u0_T hG hu0 hcon hbg h3 (r.restr g')
          simp only [gtTube]
          rw [ungAt, if_pos hP', if_pos ((hG.fibT _ _ hP').elKV _ _ _ hm)]
        · rw [if_neg h3, if_neg hno]
  base n' h hh := by
    set b := (g.comp (Hom.wk k)).comp h with hbdef
    have hb : ((gtδ φ).restr b).holds := by
      rw [hbdef, Hom.comp_assoc]; exact gt_δ_comp hG hg ((Hom.wk k).comp h)
    obtain ⟨htf, htf0, -⟩ := gt_tfill hG hψ hu0 hcon hg
    obtain ⟨-, hf0, -, -⟩ := gt_fillA hG hψ hu0 hcon
    have hgw := gt_δ_comp hG hg (Hom.wk k)
    have eB : res h (gtΩBase ep u0 g) = eqFun n' (dat ep n' (Hom.snoc b (DM.zero n'))) (res b u0) := by
      rw [gtΩBase, gt_e_res hG (gt_δ_snoc hG.cof hgw _) (gt_u0_T0 hG hu0 hgw) h, Hom.snoc_comp, DM.zero_restr,
        res_res]
    rw [eB]
    unfold gtΩTube
    rw [← hbdef]
    split_ifs with h1 h2
    · rfl
    · congr 1
      rw [show Hom.snoc ((Hom.wk k).comp h) (DM.zero n') = (eZ k).comp ((Hom.wk k).comp h) from snoc_zero_eq _,
        ← res_res, htf0, res_res]
      rfl
    · rw [show Hom.snoc b (DM.zero n') = (eZ n).comp b from snoc_zero_eq _, ← res_res, hf0, gtA0,
        hG.ung_res hu0, ← snoc_zero_eq]
      have hP := gt_δ_snoc hG.cof hb (DM.zero n')
      have hm := gt_u0_T0 hG hu0 hb
      rw [ungAt, if_pos hP, if_pos ((hG.fibT _ _ hP).elKV _ _ _ hm)]

end gtΩ3

section gtΩ4

variable {A : V} {φ : Cof (n + 1)} {Tp ep : V} (hG : GlueOK A φ Tp ep) {ψ : Cof n} (hψ : ψ.IsCof)
  {u0 : V} (hu0 : u0 ∈ El (glueC (n + 1) A φ Tp ep) (eZ n))
  (hcon : ConstOn (glueC (n + 1) A φ Tp ep) (Hom.id (n + 1)) ψ)

include hG hψ hu0 hcon in
theorem gt_A1'_restr_face {g : Hom k n} (hg : (ψ.restr g).holds) :
    res g (gtA1' A φ ep ψ u0) = ungAt k (φ.restr (Hom.snoc g (DM.one k))) (dat ep k (Hom.snoc g (DM.one k))) (res g u0) :=
  compF_restr_face hG.fibA hψ (gt_A0_mem hG hu0) (gt_tube_ok hG hu0 hcon) g hg

include hG hψ hu0 hcon in
theorem gt_Ω_mem {g : Hom k n} (hg : ((gtδ φ).restr g).holds) :
    gtΩ A φ Tp ep ψ u0 g ∈ El (res (Hom.wk k) (gtAA1 A g)) (Hom.id (k + 1)) := by
  have := compF_mem hG.fibA (isCof_pathFace (hψ.restr g)) (gt_ΩBase_mem hG hu0 hg) (gt_Ω_ok hG hψ hu0 hcon hg)
  rw [show Hom.endpt (k + 1) (DM.one (k + 1)) = Hom.snoc (Hom.id (k + 1)) (DM.one (k + 1)) from rfl,
    gtΩLine_snoc, Hom.comp_id, snoc_one_eq] at this
  rw [gtAA1, El_res, El_res, Hom.comp_id]; exact this

include hG hψ hu0 hcon in
theorem gt_Ω_endpt0 {g : Hom k n} (hg : ((gtδ φ).restr g).holds) :
    res (Hom.endpt k (DM.zero k)) (gtΩ A φ Tp ep ψ u0 g) = eqFun k (gtE1 ep g) (gtT1' Tp ψ u0 g) := by
  have hface : ((pathFace (ψ.restr g)).restr (Hom.endpt k (DM.zero k))).holds := by
    rw [pathFace, Cof.or_restr, Cof.or_restr, Cof.holds_or, Cof.holds_or, Cof.eq0_restr,
      lastVar_restr_endpt, Cof.eq0_zero]; exact Or.inr (Or.inl Cof.holds_top)
  rw [gtΩ, compF_restr_face hG.fibA (isCof_pathFace (hψ.restr g)) (gt_ΩBase_mem hG hu0 hg)
    (gt_Ω_ok hG hψ hu0 hcon hg) _ hface]
  have hb : (g.comp (Hom.wk k)).comp (Hom.endpt k (DM.zero k)) = g := by
    rw [Hom.comp_assoc, Hom.wk_comp_endpt, Hom.comp_id]
  unfold gtΩTube
  rw [hb, gtE1, ← snoc_one_eq]
  obtain ⟨-, -, -⟩ := gt_tfill hG hψ hu0 hcon hg
  by_cases h1 : (ψ.restr g).holds
  · rw [if_pos h1, gtT1', (gt_TL_fib hG hg).trFace k _ _ _ (hψ.restr g) (gt_TL_const hG hcon hg)
      (gt_u0_TL hG hu0 hg) h1]
  · have h2 : ((Cof.eq0 (lastVar k)).restr (Hom.endpt k (DM.zero k))).holds := by
      rw [Cof.eq0_restr, lastVar_restr_endpt, Cof.eq0_zero]; exact Cof.holds_top
    rw [if_neg h1, if_pos h2, Hom.wk_comp_endpt, show Hom.snoc (Hom.id k) (DM.one k) = eO k from rfl,
      transpFillF_endpt1 (gt_TL_fib hG hg) (hψ.restr g) (gt_TL_const hG hcon hg) (gt_u0_TL hG hu0 hg)]
    rfl

include hG hψ hu0 hcon in
theorem gt_Ω_endpt1 {g : Hom k n} (hg : ((gtδ φ).restr g).holds) :
    res (Hom.endpt k (DM.one k)) (gtΩ A φ Tp ep ψ u0 g) = res g (gtA1' A φ ep ψ u0) := by
  have hface : ((pathFace (ψ.restr g)).restr (Hom.endpt k (DM.one k))).holds := by
    rw [pathFace, Cof.or_restr, Cof.or_restr, Cof.holds_or, Cof.holds_or, Cof.eq1_restr,
      lastVar_restr_endpt, Cof.eq1_one]; exact Or.inr (Or.inr Cof.holds_top)
  rw [gtΩ, compF_restr_face hG.fibA (isCof_pathFace (hψ.restr g)) (gt_ΩBase_mem hG hu0 hg)
    (gt_Ω_ok hG hψ hu0 hcon hg) _ hface]
  have hb : (g.comp (Hom.wk k)).comp (Hom.endpt k (DM.one k)) = g := by
    rw [Hom.comp_assoc, Hom.wk_comp_endpt, Hom.comp_id]
  unfold gtΩTube
  rw [hb]
  by_cases h1 : (ψ.restr g).holds
  · have hP := gt_δ_snoc hG.cof hg (DM.one k)
    rw [if_pos h1, gt_A1'_restr_face hG hψ hu0 hcon h1, ungAt, if_pos hP,
      if_pos ((hG.fibT _ _ hP).elKV _ _ _ (gt_u0_T hG hu0 hcon hg h1 _))]
  · have h2 : ¬ ((Cof.eq0 (lastVar k)).restr (Hom.endpt k (DM.one k))).holds := by
      rw [eq0_restr_holds_iff, lastVar_restr_endpt]; exact DM.zero_ne_one'.symm
    rw [if_neg h1, if_neg h2, snoc_one_eq, ← res_res, (gt_fillA hG hψ hu0 hcon).2.2.1]

include hG hψ hu0 hcon in
theorem gt_ω_mem {g : Hom k n} (hg : ((gtδ φ).restr g).holds) :
    gtω A φ Tp ep ψ u0 g ∈ El (pathC k (res (Hom.wk k) (gtAA1 A g)) (eqFun k (gtE1 ep g) (gtT1' Tp ψ u0 g))
      (res g (gtA1' A φ ep ψ u0))) (Hom.id k) := by
  have hT1 := gt_T1'_mem hG hψ hu0 hcon hg
  have hP1 : (φ.restr ((eO n).comp g)).holds := by rw [← snoc_one_eq]; exact gt_δ_snoc hG.cof hg _
  have hekv : IsKV k (eqFun k (gtE1 ep g) (gtT1' Tp ψ u0 g)) :=
    (hG.fibA.restr _).elKV _ _ _ (by
      have := gt_e_mem hG hP1 hT1; rw [El_eq_res_id] at this; exact this)
  have hakv : IsKV k (res g (gtA1' A φ ep ψ u0)) := isKV_res _ _
  rw [El_pathC, Hom.lift_id, res_id (isKV_res _ _), res_id hekv, res_id hakv, pathElSet, mem_pathEl]
  exact ⟨_, gt_Ω_mem hG hψ hu0 hcon hg, rfl, gt_Ω_endpt0 hG hψ hu0 hcon hg, gt_Ω_endpt1 hG hψ hu0 hcon hg⟩

end gtΩ4

theorem gtΩLine_lift (g : Hom k n) (h : Hom n' k) :
    (gtΩLine g).comp (Hom.lift (Hom.lift h)) = gtΩLine (g.comp h) := by
  apply Hom.ext_snoc
  · intro p; apply funext; intro j; simp [gtΩLine]
  · intro p; simp [gtΩLine]

section gtΩ5

variable {A : V} {φ : Cof (n + 1)} {Tp ep : V} (hG : GlueOK A φ Tp ep) {ψ : Cof n} (hψ : ψ.IsCof)
  {u0 : V} (hu0 : u0 ∈ El (glueC (n + 1) A φ Tp ep) (eZ n))
  (hcon : ConstOn (glueC (n + 1) A φ Tp ep) (Hom.id (n + 1)) ψ)

include hG hψ hu0 hcon in
theorem gt_tfill_res {g : Hom k n} (hg : ((gtδ φ).restr g).holds) (h : Hom n' k) :
    res (Hom.lift h) (transpFillF (gtTL Tp g) (Hom.id (k + 1)) (ψ.restr g) (res g u0)) =
      transpFillF (gtTL Tp (g.comp h)) (Hom.id (n' + 1)) (ψ.restr (g.comp h)) (res (g.comp h) u0) := by
  rw [transpFillF_natural (gt_TL_fib hG hg) (hψ.restr g) (gt_TL_const hG hcon hg) (gt_u0_TL hG hu0 hg),
    ← transpFillF_res_id, Hom.id_comp, gt_TL_res hG hg, Hom.lift_comp, Cof.restr_restr, res_res, gtTL]

include hG hψ hu0 hcon in
/-- `ω` is natural. -/
theorem gt_Ω_res {g : Hom k n} (hg : ((gtδ φ).restr g).holds) (h : Hom n' k) :
    res (Hom.lift h) (gtΩ A φ Tp ep ψ u0 g) = gtΩ A φ Tp ep ψ u0 (g.comp h) := by
  rw [gtΩ, compF_res hG.fibA (isCof_pathFace (hψ.restr g)) (gt_ΩBase_mem hG hu0 hg) (gt_Ω_ok hG hψ hu0 hcon hg),
    gtΩLine_lift, pathFace_restr_lift, Cof.restr_restr, gtΩ]
  have hgw := gt_δ_comp hG hg (Hom.wk k)
  congr 1
  · funext n'' h' r
    simp only [Tube.restr, gtΩTube, ← Hom.comp_assoc]
    rw [Hom.comp_assoc g (Hom.wk k) (Hom.lift h), Hom.wk_comp_lift, ← Hom.comp_assoc,
      show (Cof.eq0 (lastVar k)).restr ((Hom.lift h).comp h') = (Cof.eq0 (lastVar n')).restr h' by
        rw [← Cof.restr_restr, Cof.eq0_restr, lastVar_restr_lift]]
    split_ifs
    · rfl
    · rw [← gt_tfill_res hG hψ hu0 hcon hg h, res_res, lift_comp_snoc]
      rfl
    · rfl
  · rw [gtΩBase, gtΩBase, gt_e_res hG (gt_δ_snoc hG.cof hgw _) (gt_u0_T0 hG hu0 hgw), Hom.snoc_comp,
      res_res, Hom.comp_assoc, Hom.wk_comp_lift, ← Hom.comp_assoc, DM.zero_restr]

include hG hψ hu0 hcon in
theorem gt_ω_res {g : Hom k n} (hg : ((gtδ φ).restr g).holds) (h : Hom n' k) :
    res h (gtω A φ Tp ep ψ u0 g) = gtω A φ Tp ep ψ u0 (g.comp h) := by
  rw [gtω, res_pathOfLine, gt_Ω_res hG hψ hu0 hcon hg h, gtω]

end gtΩ5

/-! ### The contractibility data, on `φ(1)` -/

section gtC

variable {A : V} {φ : Cof (n + 1)} {Tp ep : V} (hG : GlueOK A φ Tp ep) {ψ : Cof n} (hψ : ψ.IsCof)
  {u0 : V} (hu0 : u0 ∈ El (glueC (n + 1) A φ Tp ep) (eZ n))
  (hcon : ConstOn (glueC (n + 1) A φ Tp ep) (Hom.id (n + 1)) ψ)

include hG hψ hu0 hcon in
theorem gt_A1'_g (g : Hom k n) : res g (gtA1' A φ ep ψ u0) ∈ El (gtAA1 A g) (Hom.id k) := by
  have := hG.fibA.elRes _ _ _ (gt_A1'_mem hG hψ hu0 hcon) k g
  rw [Hom.id_comp] at this
  rw [gtAA1, El_res, Hom.comp_id]; exact this

include hG in
theorem gt_e1 {g : Hom k n} (hg : (φ.restr ((eO n).comp g)).holds) :
    Fib (gtT1 Tp g) k ∧ Fib (gtAA1 A g) k ∧
      fstV k (gtE1 ep g) ∈ El (arrowM k (gtT1 Tp g) (gtAA1 A g)) (Hom.id k) ∧
      sndV k (gtE1 ep g) ∈ piElSet k (gtAA1 A g) (famV k (gtAA1 A g) fun k' g' y =>
        isContrM k' (fiberM k' (res g' (gtT1 Tp g)) (res g' (gtAA1 A g)) (res g' (fstV k (gtE1 ep g))) y)) := by
  have hT := hG.fibT k _ hg
  have hA := hG.fibA.restr ((eO n).comp g)
  have he := hG.mem_e k _ hg
  rw [equivCode_eq_equivM hT hA] at he
  obtain ⟨p, hp, q, hq, he'⟩ := mem_equivM hT hA he
  have hpkv : IsKV k p := (mem_piEl.1 (mem_arrowM hT.kv hp)).1
  have hqkv : IsKV k q := (mem_piEl.1 hq).1
  refine ⟨hT, hA, ?_, ?_⟩
  · unfold gtE1 gtT1 gtAA1; rw [he', fstV_pairV hpkv]; exact hp
  · unfold gtE1 gtT1 gtAA1; rw [he', fstV_pairV hpkv, sndV_pairV hqkv]; exact hq

include hG hψ hu0 hcon in
theorem gt_c {g : Hom k n} (hg : (φ.restr ((eO n).comp g)).holds) :
    Fib (gtFib A φ Tp ep ψ u0 g) k ∧
    fstV k (gtC A φ ep ψ u0 g) ∈ El (gtFib A φ Tp ep ψ u0 g) (Hom.id k) ∧
    sndV k (gtC A φ ep ψ u0 g) ∈ piElSet k (gtFib A φ Tp ep ψ u0 g) (famV k (gtFib A φ Tp ep ψ u0 g)
      fun k' h x => pathC k' (res (Hom.wk k') (res h (gtFib A φ Tp ep ψ u0 g))) (res h (fstV k (gtC A φ ep ψ u0 g))) x) ∧
    gtC A φ ep ψ u0 g = pairV k (fstV k (gtC A φ ep ψ u0 g)) (sndV k (gtC A φ ep ψ u0 g)) := by
  obtain ⟨hT, hA, hp, hq⟩ := gt_e1 hG hg
  have ha := gt_A1'_g hG hψ hu0 hcon g
  have hfib : Fib (gtFib A φ Tp ep ψ u0 g) k := fib_fiberM hT hA hp ha
  have hc := appV_mem_piElSet hq ha
  rw [apZ_dat_famV _ _ _ ha, res_id hT.kv, res_id hA.kv,
    res_id (mem_piEl.1 (mem_arrowM hT.kv hp)).1] at hc
  obtain ⟨cen, hcen, ctr, hctr, hc'⟩ := mem_isContrM hfib hc
  have hcenkv : IsKV k cen := hfib.elKV _ _ _ hcen
  have hctrkv : IsKV k ctr := (mem_piEl.1 hctr).1
  have e1 : gtC A φ ep ψ u0 g = pairV k cen ctr := hc'
  refine ⟨hfib, ?_, ?_, ?_⟩
  · rw [e1, fstV_pairV hcenkv]; exact hcen
  · rw [e1, fstV_pairV hcenkv, sndV_pairV hctrkv]; exact hctr
  · rw [e1, fstV_pairV hcenkv, sndV_pairV hctrkv]

end gtC

section gtNat

variable {A : V} {φ : Cof (n + 1)} {Tp ep : V} (hG : GlueOK A φ Tp ep) {ψ : Cof n} (hψ : ψ.IsCof)
  {u0 : V} (hu0 : u0 ∈ El (glueC (n + 1) A φ Tp ep) (eZ n))
  (hcon : ConstOn (glueC (n + 1) A φ Tp ep) (Hom.id (n + 1)) ψ)

theorem fstV_res_of_pair {v : V} (hv : v = pairV k (fstV k v) (sndV k v)) (h : Hom n' k) :
    fstV n' (res h v) = res h (fstV k v) := by
  rw [hv, res_pairV, fstV_pairV (isKV_res _ _), ← hv]

theorem sndV_res_of_pair {v : V} (hv : v = pairV k (fstV k v) (sndV k v)) (h : Hom n' k) :
    sndV n' (res h v) = res h (sndV k v) := by
  rw [hv, res_pairV, sndV_pairV (isKV_res _ _), ← hv]

include hG in
theorem gt_e1_pair {g : Hom k n} (hg : (φ.restr ((eO n).comp g)).holds) :
    gtE1 ep g = pairV k (fstV k (gtE1 ep g)) (sndV k (gtE1 ep g)) := by
  have hT := hG.fibT k _ hg
  have hA := hG.fibA.restr ((eO n).comp g)
  have he := hG.mem_e k _ hg
  rw [equivCode_eq_equivM hT hA] at he
  obtain ⟨p, hp, q, hq, he'⟩ := mem_equivM hT hA he
  have hpkv : IsKV k p := (mem_piEl.1 (mem_arrowM hT.kv hp)).1
  have hqkv : IsKV k q := (mem_piEl.1 hq).1
  unfold gtE1 at *; rw [he', fstV_pairV hpkv, sndV_pairV hqkv]

include hG in
theorem gt_e1_res {g : Hom k n} (hg : (φ.restr ((eO n).comp g)).holds) (h : Hom n' k) :
    res h (gtE1 ep g) = gtE1 ep (g.comp h) := hG.ecoh k _ hg n' h

include hG in
theorem gt_T1_res {g : Hom k n} (hg : (φ.restr ((eO n).comp g)).holds) (h : Hom n' k) :
    res h (gtT1 Tp g) = gtT1 Tp (g.comp h) := hG.Tcoh k _ hg n' h

theorem gt_AA1_res (g : Hom k n) (h : Hom n' k) : res h (gtAA1 A g) = gtAA1 A (g.comp h) := by
  unfold gtAA1; rw [res_res]; rfl

include hG in
theorem gt_φ1_comp {g : Hom k n} (hg : (φ.restr ((eO n).comp g)).holds) (h : Hom n' k) :
    (φ.restr ((eO n).comp (g.comp h))).holds := by
  rw [← Hom.comp_assoc, ← Cof.restr_restr]; exact (hG.cof.restr _).holds_restr hg h

include hG hψ hu0 hcon in
theorem gt_fib_res {g : Hom k n} (hg : (φ.restr ((eO n).comp g)).holds) (h : Hom n' k) :
    res h (gtFib A φ Tp ep ψ u0 g) = gtFib A φ Tp ep ψ u0 (g.comp h) := by
  unfold gtFib
  rw [res_fiberM, gt_T1_res hG hg, gt_AA1_res, ← fstV_res_of_pair (gt_e1_pair hG hg) h, gt_e1_res hG hg, res_res]

include hG hψ hu0 hcon in
theorem gt_C_res {g : Hom k n} (hg : (φ.restr ((eO n).comp g)).holds) (h : Hom n' k) :
    res h (gtC A φ ep ψ u0 g) = gtC A φ ep ψ u0 (g.comp h) := by
  obtain ⟨-, -, -, hq⟩ := gt_e1 hG hg
  unfold gtC
  rw [res_appV hq (gt_A1'_g hG hψ hu0 hcon g) h, ← sndV_res_of_pair (gt_e1_pair hG hg) h, gt_e1_res hG hg,
    res_res]

include hG hψ hu0 hcon in
theorem gt_T1'_res {g : Hom k n} (hg : ((gtδ φ).restr g).holds) (h : Hom n' k) :
    res h (gtT1' Tp ψ u0 g) = gtT1' Tp ψ u0 (g.comp h) := by
  unfold gtT1'
  rw [(gt_TL_fib hG hg).trRes k _ _ _ (hψ.restr g) (gt_TL_const hG hcon hg) (gt_u0_TL hG hu0 hg) n' h,
    Hom.id_comp, transpAt_eq_res_id, gt_TL_res hG hg, Hom.lift_comp, Cof.restr_restr, res_res]
  rfl

end gtNat

/-! ### The extension `ext` -/

section gtExt

variable {A : V} {φ : Cof (n + 1)} {Tp ep : V} (hG : GlueOK A φ Tp ep) {ψ : Cof n} (hψ : ψ.IsCof)
  {u0 : V} (hu0 : u0 ∈ El (glueC (n + 1) A φ Tp ep) (eZ n))
  (hcon : ConstOn (glueC (n + 1) A φ Tp ep) (Hom.id (n + 1)) ψ)

/-- The tube `j ↦ ctr(y)(j)` of a contraction, on a face where the partial element `y` is given. -/
theorem contr_tube_ok {X cen ctr : V} (hX : Fib X k) (hcen : cen ∈ El X (Hom.id k))
    (hctr : ctr ∈ piElSet k X (famV k X fun k' h x => pathC k' (res (Hom.wk k') (res h X)) (res h cen) x))
    {D : Cof k} {y : (n : ℕ) → Hom n k → V}
    (hy : ∀ n (h : Hom n k), (D.restr h).holds → y n h ∈ El X h)
    (hycoh : ∀ n (h : Hom n k), (D.restr h).holds → ∀ n' (g : Hom n' n), res g (y n h) = y n' (h.comp g)) :
    TubeOK X (Hom.id k) D (fun n h r => pappV n (appV n (res h ctr) (y n h)) r) cen := by
  simp only [piElSet, mem_piEl] at hctr
  have key : ∀ n (h : Hom n k), (D.restr h).holds → ∃ p, p ∈ El X (h.comp (Hom.wk n)) ∧
      appV n (res h ctr) (y n h) = pathOfLine n p ∧ res (Hom.endpt n (DM.zero n)) p = res h cen := by
    intro n h hd
    have hP := (hctr.2.1 n h).2 (y n h) (hy n h hd)
    rw [apZ_dat_famV _ _ _ (hy n h hd)] at hP
    obtain ⟨p, hp, e, h0, -⟩ := mem_pathC.1 hP
    rw [Hom.lift_id, El_res, El_res, Hom.comp_id] at hp
    rw [res_id (isKV_res _ _)] at h0
    exact ⟨p, hp, by rw [appV_res, e], h0⟩
  refine ⟨fun n h r hd => ?_, fun n h r hd n' g => ?_, fun n h hd => ?_⟩
  · obtain ⟨p, hp, e, -⟩ := key n h hd
    have := hX.elRes _ _ _ hp _ (Hom.endpt n r)
    rw [Hom.comp_assoc, Hom.wk_comp_endpt, Hom.comp_id] at this
    rw [Hom.id_comp, e, pappV_pathOfLine]; exact this
  · obtain ⟨p, hp, e, -⟩ := key n h hd
    rw [e, res_pappV_pathOfLine, ← e, appV_res, appV_res,
      hctr.2.2 n h _ (hy n h hd) n' g, hycoh n h hd n' g]
  · obtain ⟨p, -, e, h0⟩ := key n h hd
    rw [e, pappV_pathOfLine, h0]

include hG hψ hu0 hcon in
theorem gt_Ω_psi {g : Hom k n} (hg : ((gtδ φ).restr g).holds) (hψg : (ψ.restr g).holds) :
    gtΩ A φ Tp ep ψ u0 g = res (Hom.wk k) (res g (gtA1' A φ ep ψ u0)) := by
  have hface : (pathFace (ψ.restr g)).holds := by
    rw [pathFace, Cof.holds_or]; left; exact ((hψ.restr g).holds_restr hψg _)
  have hgw := gt_δ_comp hG hg (Hom.wk k)
  have hψgw : (ψ.restr (g.comp (Hom.wk k))).holds := by
    rw [← Cof.restr_restr]; exact (hψ.restr g).holds_restr hψg _
  rw [gtΩ, compF_face hG.fibA (isCof_pathFace (hψ.restr g)) (gt_ΩBase_mem hG hu0 hg)
    (gt_Ω_ok hG hψ hu0 hcon hg) hface]
  unfold gtΩTube
  rw [Hom.comp_id, if_pos hψgw, res_res, gt_A1'_restr_face hG hψ hu0 hcon hψgw]
  have hP := gt_δ_snoc hG.cof hgw (DM.one (k + 1))
  rw [ungAt, if_pos hP, if_pos ((hG.fibT _ _ hP).elKV _ _ _ (gt_u0_T hG hu0 hcon hgw hψgw _))]

include hG hu0 hcon in
theorem gt_u0_T1 {g : Hom k n} (hψg : (ψ.restr g).holds) (hφg : (φ.restr ((eO n).comp g)).holds) :
    res g u0 ∈ El (gtT1 Tp g) (Hom.id k) := by
  have h0 := gt_u_mem hG hu0 hcon hψg (DM.one k)
  rw [El_eq_res_id, snoc_one_eq, res_glueC hG.Tcoh (fun k f hf => (hG.fibT k f hf).kv) hG.cof, if_pos hφg] at h0
  exact h0

include hG hψ hu0 hcon in
theorem gt_A1'_psi {g : Hom k n} (hψg : (ψ.restr g).holds) (hφg : (φ.restr ((eO n).comp g)).holds) :
    res g (gtA1' A φ ep ψ u0) = eqFun k (gtE1 ep g) (res g u0) := by
  rw [gt_A1'_restr_face hG hψ hu0 hcon hψg, ungAt, snoc_one_eq, if_pos hφg,
    if_pos ((hG.fibT _ _ hφg).elKV _ _ _ (gt_u0_T1 hG hu0 hcon hψg hφg))]
  rfl

include hG hψ hu0 hcon in
theorem gt_refl_mem {g : Hom k n} (hψg : (ψ.restr g).holds) (hφg : (φ.restr ((eO n).comp g)).holds) :
    pairV k (res g u0) (pathOfLine k (res (Hom.wk k) (res g (gtA1' A φ ep ψ u0)))) ∈
      El (gtFib A φ Tp ep ψ u0 g) (Hom.id k) := by
  obtain ⟨hT, hA, hp, -⟩ := gt_e1 hG hφg
  have ha := gt_A1'_g hG hψ hu0 hcon g
  have hakv : IsKV k (res g (gtA1' A φ ep ψ u0)) := isKV_res _ _
  have hfkv : IsKV k (fstV k (gtE1 ep g)) := (mem_piEl.1 (mem_arrowM hT.kv hp)).1
  refine pairV_mem_fiberM hT.kv hA.kv hfkv hakv (gt_u0_T1 hG hu0 hcon hψg hφg) ?_
  have e := gt_A1'_psi hG hψ hu0 hcon hψg hφg
  rw [mem_pathC, Hom.lift_id]
  refine ⟨_, ?_, rfl, ?_, ?_⟩
  · have := hA.elRes _ _ _ ha (k + 1) (Hom.wk k)
    rw [Hom.id_comp] at this; rw [El_res, Hom.comp_id]; exact this
  · rw [res_res, Hom.wk_comp_endpt, res_id hakv,
      show appV k (fstV k (gtE1 ep g)) (res g u0) = res g (gtA1' A φ ep ψ u0) from e.symm, res_id hakv]
  · rw [res_res, Hom.wk_comp_endpt]

theorem cof_holds_comp {m : ℕ} {χ : Cof m} (hχ : χ.IsCof) {g : Hom k m} (hg : (χ.restr g).holds) (h : Hom n' k) :
    (χ.restr (g.comp h)).holds := by
  rw [← Cof.restr_restr]; exact (hχ.restr g).holds_restr hg h

theorem gt_refl_res (g : Hom k n) (h : Hom n' k) :
    res h (pairV k (res g u0) (pathOfLine k (res (Hom.wk k) (res g (gtA1' A φ ep ψ u0))))) =
      pairV n' (res (g.comp h) u0) (pathOfLine n' (res (Hom.wk n') (res (g.comp h) (gtA1' A φ ep ψ u0)))) := by
  rw [res_pairV, res_pathOfLine, res_res, res_res, res_res, res_res, Hom.wk_comp_lift, Hom.comp_assoc]

include hG hψ hu0 hcon in
/-- On `δ ∧ ψ`, `(t1', ω) = (u0, refl)`. -/
theorem gt_pair_psi {g : Hom k n} (hg : ((gtδ φ).restr g).holds) (hψg : (ψ.restr g).holds) :
    pairV k (gtT1' Tp ψ u0 g) (gtω A φ Tp ep ψ u0 g) =
      pairV k (res g u0) (pathOfLine k (res (Hom.wk k) (res g (gtA1' A φ ep ψ u0)))) := by
  rw [gtω, gt_Ω_psi hG hψ hu0 hcon hg hψg, gtT1',
    (gt_TL_fib hG hg).trFace k _ _ _ (hψ.restr g) (gt_TL_const hG hcon hg) (gt_u0_TL hG hu0 hg) hψg]

include hG hψ hu0 hcon in
theorem gt_ext_tube_ok {g : Hom k n} (hφg : (φ.restr ((eO n).comp g)).holds) :
    TubeOK (gtFib A φ Tp ep ψ u0 g) (Hom.id k) (Cof.or ((gtδ φ).restr g) (ψ.restr g))
      (gtExtTube A φ Tp ep ψ u0 g) (fstV k (gtC A φ ep ψ u0 g)) := by
  obtain ⟨hX, hcen, hctr, -⟩ := gt_c hG hψ hu0 hcon hφg
  have hδc := gt_δ_cof (φ := φ) hG.cof
  refine contr_tube_ok hX hcen hctr (fun n' h hd => ?_) (fun n' h hd n'' g' => ?_)
  · rw [El_eq_res_id, gt_fib_res hG hψ hu0 hcon hφg]
    rw [Cof.or_restr, Cof.holds_or, Cof.restr_restr, Cof.restr_restr] at hd
    split_ifs with hδ
    · have hP1 : (φ.restr ((eO n).comp (g.comp h))).holds := by rw [← snoc_one_eq]; exact gt_δ_snoc hG.cof hδ _
      obtain ⟨hT, hA, hp, -⟩ := gt_e1 hG hP1
      exact pairV_mem_fiberM hT.kv hA.kv (mem_piEl.1 (mem_arrowM hT.kv hp)).1 (isKV_res _ _)
        (gt_T1'_mem hG hψ hu0 hcon hδ) (gt_ω_mem hG hψ hu0 hcon hδ)
    · exact gt_refl_mem hG hψ hu0 hcon (hd.resolve_left hδ) (by
        rw [← Hom.comp_assoc]; exact cof_holds_comp hG.cof hφg h)
  · rw [Cof.or_restr, Cof.holds_or, Cof.restr_restr, Cof.restr_restr] at hd
    have e : g.comp (h.comp g') = (g.comp h).comp g' := (Hom.comp_assoc _ _ _).symm
    by_cases hδ : ((gtδ φ).restr (g.comp h)).holds
    · rw [if_pos hδ, show g.comp (h.comp g') = (g.comp h).comp g' from e, if_pos (cof_holds_comp hδc hδ g'),
        res_pairV, gt_T1'_res hG hψ hu0 hcon hδ, gt_ω_res hG hψ hu0 hcon hδ]
    · rw [if_neg hδ, gt_refl_res, show g.comp (h.comp g') = (g.comp h).comp g' from e]
      split_ifs with hδ'
      · rw [gt_pair_psi hG hψ hu0 hcon hδ' (cof_holds_comp hψ (hd.resolve_left hδ) g')]
      · rfl

end gtExt

section fields

variable {A : V} {φ : Cof m} {Tp ep : V} (hG : GlueOK A φ Tp ep)
include hG

/-! ### The transport fields of the fibration structure -/

theorem GlueOK.trMem (n : ℕ) (f : Hom (n + 1) m) (ψ : Cof n) (a0 : V) (hψ : ψ.IsCof)
    (hc : ConstOn (glueC m A φ Tp ep) f ψ) (ha : a0 ∈ El (glueC m A φ Tp ep) (f.comp (Hom.endpt n (DM.zero n)))) :
    transpAt (glueC m A φ Tp ep) f ψ a0 ∈ El (glueC m A φ Tp ep) (f.comp (Hom.endpt n (DM.one n))) := by
  sorry

theorem GlueOK.trFace (n : ℕ) (f : Hom (n + 1) m) (ψ : Cof n) (a0 : V) (hψ : ψ.IsCof)
    (hc : ConstOn (glueC m A φ Tp ep) f ψ) (ha : a0 ∈ El (glueC m A φ Tp ep) (f.comp (Hom.endpt n (DM.zero n))))
    (hh : ψ.holds) : transpAt (glueC m A φ Tp ep) f ψ a0 = a0 := by
  sorry

theorem GlueOK.trRes (n : ℕ) (f : Hom (n + 1) m) (ψ : Cof n) (a0 : V) (hψ : ψ.IsCof)
    (hc : ConstOn (glueC m A φ Tp ep) f ψ) (ha : a0 ∈ El (glueC m A φ Tp ep) (f.comp (Hom.endpt n (DM.zero n))))
    (n' : ℕ) (h : Hom n' n) :
    res h (transpAt (glueC m A φ Tp ep) f ψ a0) =
      transpAt (glueC m A φ Tp ep) (f.comp (Hom.lift h)) (ψ.restr h) (res h a0) := by
  sorry

/-- Glue codes are fibrant. -/
theorem GlueOK.fib : Fib (glueC m A φ Tp ep) m where
  kv := isKV_glueC _ _ _ _
  elKV _ _ _ hv := hG.elKV hv
  elRes _ _ _ hv _ h := hG.elRes hv h
  hcMem := hG.hcMem
  hcFace := hG.hcFace
  hcRes := hG.hcRes
  trMem := hG.trMem
  trFace := hG.trFace
  trRes := hG.trRes

end fields

end

end Model
