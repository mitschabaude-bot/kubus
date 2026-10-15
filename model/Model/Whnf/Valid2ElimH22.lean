import Model.Whnf.Valid2ElimH21

/-! # The full formal composition computation rule for HIT elimination -/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

variable {S : Sig} {Ψ k : ℕ} {Φ : I} {Γ : Ctx} (hW : WfSig S)
include hW

/-- Closing a valid tube gives its same-point relation. -/
theorem tubeD_of_valid {A u : Tm} {φ : I} (hφ : φ.Scoped Ψ)
    (hv : Valid2 S (Ψ + 1) (cof Φ φ).shift Γ.dshift u u A.dshift) (c : CSub2 S Ψ Φ Γ k) :
    TubeD S k (c.L A) (φ.subst c.σ.τ) ((c.up hW).L u) ((c.up hW).R u) := by
  intro k' σ r hr hh
  have R := (hv k' (((c.restr hW σ).cof (holds_restr hh hφ)).cons r r hr hr (I_eq_refl _))).2
  rw [CSub2.L_cons hW, CSub2.L_cons hW, CSub2.R_cons hW] at R
  change RE2 S k' ((((c.restr hW σ).up hW).L A.dshift).dinst r)
    ((((c.restr hW σ).up hW).L u).dinst r) ((((c.restr hW σ).up hW).R u).dinst r) at R
  rw [show ((((c.restr hW σ).up hW).L A.dshift).dinst r) = (c.restr hW σ).L A by
    show ((A.dshift.subst (dupS (c.restr hW σ).γ) (I.up (c.restr hW σ).σ.τ)).dinst r) = _
    rw [dshift_dup_subst, dshift_dinst], CSub2.restr_L, CSub2.up_restr_L, CSub2.up_restr_R] at R
  exact R

omit hW in
theorem elimLine_consL {d : ℕ} {ps M bs u : Tm} (c : CSub2 S Ψ Φ Γ k) (r : I) (hr : r.Scoped k) :
    (c.cons r r hr hr (I_eq_refl _)).L (.elim d ps.dshift M.dshift bs.dshift u) =
      .elim d (c.L ps) (M.subst (Tm.up c.γ) c.σ.τ) (c.L bs)
        ((c.cons r r hr hr (I_eq_refl _)).L u) := by
  simp only [CSub2.L, CSub2.cons, Tm.subst, ISub.cons]
  simp only [dshift_subst]

omit hW in
theorem elimLine_consR {d : ℕ} {ps M bs u : Tm} (c : CSub2 S Ψ Φ Γ k) (r : I) (hr : r.Scoped k) :
    (c.cons r r hr hr (I_eq_refl _)).R (.elim d ps.dshift M.dshift bs.dshift u) =
      .elim d (c.R ps) (M.subst (Tm.up c.γ') c.σ'.τ) (c.R bs)
        ((c.cons r r hr hr (I_eq_refl _)).R u) := by
  simp only [CSub2.R, CSub2.cons, Tm.subst, ISub.cons]
  simp only [dshift_subst]

/-- The valid tube eliminator supplies the recursive point eliminations after closing. -/
theorem elimTube_at_valid {d : ℕ} {ps M bs u : Tm} {φ : I} (hφ : φ.Scoped Ψ)
    (hv : Valid2 S (Ψ + 1) (cof Φ φ).shift Γ.dshift
      (.elim d ps.dshift M.dshift bs.dshift u) (.elim d ps.dshift M.dshift bs.dshift u) (M.dshift.inst u))
    (c : CSub2 S Ψ Φ Γ k) (k' : ℕ) (σ : ISub k' k) (r : I) (hr : r.Scoped k')
    (hh : (ival (idEnv k') ((φ.subst c.σ.τ).subst σ.τ)).holds) :
    RE2 S k' (((M.subst (Tm.up c.γ) c.σ.τ).isub σ).inst ((((c.up hW).L u).isub σ.up).dinst r))
      (.elim d ((c.L ps).isub σ) ((M.subst (Tm.up c.γ) c.σ.τ).isub σ) ((c.L bs).isub σ)
        ((((c.up hW).L u).isub σ.up).dinst r))
      (.elim d ((c.R ps).isub σ) ((M.subst (Tm.up c.γ') c.σ'.τ).isub σ) ((c.R bs).isub σ)
        ((((c.up hW).R u).isub σ.up).dinst r)) := by
  let cp := ((c.restr hW σ).cof (holds_restr hh hφ)).cons r r hr hr (I_eq_refl _)
  have R := (hv k' cp).2
  rw [elimLine_consL, elimLine_consR] at R
  have et : cp.L (M.dshift.inst u) =
      (M.subst (Tm.up (c.restr hW σ).γ) (c.restr hW σ).σ.τ).inst (cp.L u) := by
    simp only [cp, CSub2.L, CSub2.cons, CSub2.cof, inst_subst, ISub.cons]
    simp only [dshift_subst]
  rw [et] at R
  change RE2 S k' _ (.elim d ((c.restr hW σ).L ps)
    (M.subst (Tm.up (c.restr hW σ).γ) (c.restr hW σ).σ.τ) ((c.restr hW σ).L bs) (cp.L u))
    (.elim d ((c.restr hW σ).R ps)
    (M.subst (Tm.up (c.restr hW σ).γ') (c.restr hW σ).σ'.τ) ((c.restr hW σ).R bs) (cp.R u)) at R
  have el : cp.L u = (((c.up hW).L u).isub σ.up).dinst r := c.cons_restr_L hW σ r r hr hr (I_eq_refl _) u
  have er : cp.R u = (((c.up hW).R u).isub σ.up).dinst r := c.cons_restr_R hW σ r r hr hr (I_eq_refl _) u
  simpa only [CSub2.restr_L, CSub2.restr_R, CSub2.upL_restr, CSub2.upR_restr, el, er] using R

/-- HIT composition computation follows from formation, congruence and typing inversion. -/
theorem valid_elimHcompH {d : ℕ} {D : DataDecl}
    (hD : S[d]? = some (.data D)) (hH : D.isHIT = true) (hyp : HITHyp2 S (d + 1))
    {ps M bs qs u a T : Tm} {φ : I}
    (hi : ElimInv2 S Ψ Φ Γ d ps M bs (.hcomp (.data d qs) φ u a) T)
    (hh : HcompInv S Ψ Φ Γ (.data d ps) φ u a (.data d ps))
    (hy : HasTy0 S Ψ Φ Γ (elimHcompTm d ps M bs φ u a) T)
    (hv : Valid2 S Ψ Φ Γ (.elim d ps M bs (.hcomp (.data d qs) φ u a))
      (.elim d ps M bs (.hcomp (.data d qs) φ u a)) T) :
    Valid2 S Ψ Φ Γ (.elim d ps M bs (.hcomp (.data d qs) φ u a)) (elimHcompTm d ps M bs φ u a) T := by
  have hS := sigClosed_of_wfSig hW
  obtain ⟨D0, m, E⟩ := hi.validPrem hW
  have hd := E.hD
  rw [hD] at hd
  cases hd
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, ht, htr⟩ := hi
  obtain ⟨l, hφ, -, huV, haV, hbV, -, hA, hu, ha, hb⟩ := hh
  have Eface := E.restrict hW (show (cof Φ φ).Scoped Ψ from ⟨scoped_of_ty E.hdata, hφ⟩) (ent_and_left _ _)
  have Eline := (E.dwk hW ha).restrict hW
    (KubusCore.I.scoped_shift (show (cof Φ φ).Scoped Ψ from ⟨scoped_of_ty E.hdata, hφ⟩))
    (ent_shift (ent_and_left _ _))
  have va := E.elim hW hH hyp ha haV
  have vu := Eline.elim hW hH hyp hu huV
  have vb := Eface.congr hW hH hyp hb hbV
  obtain ⟨D1, m1, Et, hx⟩ := gen_elimP ht rfl
  have hd1 := Et.hD
  rw [hD] at hd1
  cases hd1
  refine valid_redex hW hv hy ?_
  intro k c _ _
  let cr := c.diagR hW
  let PL := cr.L ps
  let ML := M.subst (Tm.up cr.γ) cr.σ.τ
  let BL := cr.L bs
  let UL := (cr.up hW).L u
  let AL := cr.L a
  let QL := cr.L qs
  let φL := φ.subst cr.σ.τ
  have hPL : HasTy S k .one [] (.data d PL) (.univ D.level) := cr.ty hW E.hdata
  have hPP : RT2 S k (.data d PL) (.data d PL) := E.dataV.ty hW cr
  have hraw : HasTy S k .one [] (.hcomp (.data d QL) φL UL AL) (.data d PL) := cr.ty hW hx
  have H : ElimRelH S d D k PL ML BL PL ML BL := elimRelH_of hW hD ht ht E.dataV E.motiveV
    (fun cc C b b' hc hb hb' => by
      rw [hb] at hb'; cases hb'; exact E.branchV cc C b hc hb) cr
  have hU : TubeD S k (.data d PL) φL UL UL := tubeD_of_valid hW hφ huV cr
  have hB : HcompBnd2 S k (.data d PL) φL UL AL := hcompBndL_at_valid hW hφ hbV cr
  have hAa : RE2 S k (.data d PL) AL AL := (haV k cr).2
  have haE : RE2 S k (ML.inst AL) (.elim d PL ML BL AL) (.elim d PL ML BL AL) := by
    simpa only [CSub2.L, CSub2.R, inst_subst, Tm.subst, PL, ML, BL, AL] using (va k cr).2
  have hclosed := closed_of_ty hW (cr.ty hW ht)
  simp only [CSub2.L, Tm.subst, Tm.closedB, Bool.and_eq_true] at hclosed
  have hpc : PL.closedB 0 k = true := hclosed.1.1.1
  have hmc : ML.closedB 1 k = true := hclosed.1.1.2
  have hbc : BL.closedB 0 k = true := hclosed.1.2
  have R := elimHcomp_compH hW hD hH hPL hPP H (ISub.id k)
    (by rw [isub_id_of_closed hpc]; exact hraw)
    (by rw [isub_id_of_closed hpc]; exact hU)
    (by rw [isub_id_of_closed hpc]; exact hAa)
    (by rw [isub_id_of_closed hpc]; exact hB)
    (by rw [isub_id_of_closed hpc, isub_id_of_closed hmc, isub_id_of_closed hbc]; exact haE)
    (by
      intro k' σ r hr hface
      simpa only [ISub.id_comp] using elimTube_at_valid hW hφ vu cr k' σ r hr hface)
    (by
      intro k' σ hface
      have R := (vb k' ((cr.restr hW σ).cof (holds_restr hface hφ))).2
      simp only [CSub2.L, CSub2.R, inst_subst, Tm.subst] at R
      change RE2 S k' ((M.subst (Tm.up (cr.restr hW σ).γ) (cr.restr hW σ).σ.τ).inst
          ((cr.restr hW σ).L (u.dinst .zero)))
        (.elim d ((cr.restr hW σ).L ps) (M.subst (Tm.up (cr.restr hW σ).γ) (cr.restr hW σ).σ.τ)
          ((cr.restr hW σ).L bs) ((cr.restr hW σ).L (u.dinst .zero)))
        (.elim d ((cr.restr hW σ).L ps) (M.subst (Tm.up (cr.restr hW σ).γ) (cr.restr hW σ).σ.τ)
          ((cr.restr hW σ).L bs) ((cr.restr hW σ).L a)) at R
      simp only [CSub2.restr_L, CSub2.upL_restr, CSub2.L_dinst hW, CSub2.up_restr_L, I.subst] at R
      simpa only [ISub.id_comp, PL, ML, BL, UL, AL] using R)
  rw [isub_id_of_closed hpc, isub_id_of_closed hmc, isub_id_of_closed hbc] at R
  have eT : cr.L (M.inst (.hcomp (.data d qs) φ u a)) = ML.inst (.hcomp (.data d QL) φL UL AL) :=
    inst_subst M (.hcomp (.data d qs) φ u a) cr.γ cr.σ.τ
  rw [← eT] at R
  have R' := htr k cr _ _ R
  have ey : cr.L (elimHcompTm d ps M bs φ u a) = elimHcompTm d PL ML BL φL UL AL := by
    exact elimHcomp_subst (σ := cr.γ) (τ := cr.σ.τ) d ps M bs φ u a
  have ex : cr.L (.elim d ps M bs (.hcomp (.data d qs) φ u a)) = .elim d PL ML BL (.hcomp (.data d QL) φL UL AL) := rfl
  change RE2 S k (cr.L T) _ _ at R'
  rw [← ey, ← ex] at R'
  exact RE2.conv hW (RT2.symm hW (hv.tyCode hW c) (hv k c).1) R'

end

end Model.Whnf
