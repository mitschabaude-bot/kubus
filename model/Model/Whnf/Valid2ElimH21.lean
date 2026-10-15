import Model.Whnf.Valid2ElimH20

/-! # Valid eliminator components under faces and interval binders -/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

variable {S : Sig} {Ψ : ℕ} {Φ : I} {Γ : Ctx} {d : ℕ} {D : DataDecl} {ps M bs : Tm} {m : ℕ}

/-- The valid premises of elimination, independently of its scrutinee. -/
structure ElimValid2 (S : Sig) (Ψ : ℕ) (Φ : I) (Γ : Ctx) (d : ℕ) (D : DataDecl) (ps M bs : Tm) (m : ℕ)
    : Prop extends ElimPrem S Ψ Φ Γ d D ps M bs m where
  dataV : Valid2 S Ψ Φ Γ (.data d ps) (.data d ps) (.univ D.level)
  paramsV : VTele2 S Ψ Φ Γ ps ps D.params []
  motiveV : Valid2 S Ψ Φ (.data d ps :: Γ) M M (.univ m)
  branchV : ∀ (c : ℕ) (C : Ctor) (b : Tm), D.ctors[c]? = some C → bs.toList[c]? = some b →
    Valid2 S Ψ Φ Γ b b (D.branchTy d c C ps M)
  boundaryV : ∀ (c : ℕ) (C : Ctor) (b : Tm) (kb : ℕ) (ψ : I) (e : Tm), D.ctors[c]? = some C →
    bs.toList[c]? = some b → C.bnd[kb]? = some (ψ, e) →
    Valid2 S (Ψ + C.dims) (cof (Φ.ren (· + C.dims)) ψ) (D.branchCtx d C ps M Γ)
      (DataDecl.branchApp C b) (D.bndElim C ps bs e) (DataDecl.branchBody d c C ps M)

variable (hW : WfSig S)
include hW

theorem ElimInv2.validPrem {t T : Tm} (h : ElimInv2 S Ψ Φ Γ d ps M bs t T) :
    ∃ D m, ElimValid2 S Ψ Φ Γ d D ps M bs m := by
  obtain ⟨D, m, hd, hp, hpt, hvp, hvd, hpm, hvm, hbs, hl, hbr, hbd, ht, -⟩ := h
  obtain ⟨D', m', E, -⟩ := gen_elimP ht rfl
  have he := E.hD
  rw [hd] at he
  cases he
  exact ⟨D, m, ⟨⟨hd, hp, E.hdata, hpt, hpm, hbs, hl, E.hbr, E.hcoh⟩, hvd, hvp, hvm, hbr, hbd⟩⟩

theorem ElimValid2.restrict {Φ' : I} (hs : Φ'.Scoped Ψ) (he : I.Entails Φ' Φ)
    (E : ElimValid2 S Ψ Φ Γ d D ps M bs m) : ElimValid2 S Ψ Φ' Γ d D ps M bs m :=
  ⟨E.toElimPrem.restrict hs he, valid_restrict hW he E.dataV, VTele2.restrict hW he E.paramsV,
    valid_restrict hW he E.motiveV,
    fun c C b hc hb => valid_restrict hW he (E.branchV c C b hc hb),
    fun c C b kb ψ e hc hb hk => valid_restrict hW
      (ent_and_mono (ent_ren he (· + C.dims)) (ent_refl _)) (E.boundaryV c C b kb ψ e hc hb hk)⟩

omit hW in
theorem toList_dshift2 (hbs : IsList bs) : bs.dshift.toList = bs.toList.map Tm.dshift := by
  simpa only [← dshift_eq] using (toList_subst hbs Tm.var (fun i => I.var (i + 1)))

/-- The valid premises can be used for an eliminator's tube. -/
theorem ElimValid2.dwk (E : ElimValid2 S Ψ Φ Γ d D ps M bs m) {t : Tm}
    (ht : HasTy0 S Ψ Φ Γ t (.data d ps)) : ElimValid2 S (Ψ + 1) Φ.shift Γ.dshift d D ps.dshift M.dshift bs.dshift m := by
  have hS := sigClosed_of_wfSig hW
  obtain ⟨D', m', E', -⟩ := gen_elimP (HasTy0.dwk hS (E.toElimPrem.elim_ty ht)) rfl
  have he := E'.hD
  rw [E.hD] at he
  cases he
  rw [upRen_id_eq] at E'
  refine ⟨⟨E.hD, E'.hps, E'.hdata, E'.hpt, HasTy0.dwk hS E.hP, E'.hbs, E'.hlen, E'.hbr, E'.hcoh⟩,
    (VTy.dwk' hW (⟨E.hdata, E.dataV⟩ : VTy S Ψ Φ Γ (.data d ps) (.univ D.level))).v,
    VTele2.dwk hW E.hpt (fun j A ha => by simpa using hS.params _ _ _ _ E.hD ha) E.paramsV,
    (VTy.dwk' hW (⟨E.hP, E.motiveV⟩ : VTy S Ψ Φ (.data d ps :: Γ) M (.univ m))).v, ?_, ?_⟩
  · intro c C b hc hb
    rw [toList_dshift2 E.hbs, List.getElem?_map] at hb
    obtain ⟨b0, hb0, rfl⟩ := Option.map_eq_some_iff.1 hb
    have hv := (VTy.dwk' hW (⟨E.hbr c C b0 hc hb0, E.branchV c C b0 hc hb0⟩ :
      VTy S Ψ Φ Γ b0 (D.branchTy d c C ps M))).v
    have e := branchTy_subst hS E.hD hc E.hps (Meta.tele_length E.hpt) M
      (σ := Tm.var) (τ := fun i => I.var (i + 1))
    have ee : (D.branchTy d c C ps M).dshift = D.branchTy d c C ps.dshift M.dshift := by
      simpa only [up_var, ← dshift_eq] using e
    rwa [ee] at hv
  · intro c C b kb ψ e hc hb hk
    rw [toList_dshift2 E.hbs, List.getElem?_map] at hb
    obtain ⟨b0, hb0, rfl⟩ := Option.map_eq_some_iff.1 hb
    exact valid_branchBnd_dwk hW E.hD hc hk E.hps (Meta.tele_length E.hpt) E.hbs
      (E.hcoh c C b0 kb ψ e hc hb0 hk) (E.boundaryV c C b0 kb ψ e hc hb0 hk)

/-- Formation applied to any valid scrutinee, using the stored valid components. -/
theorem ElimValid2.elim (hH : D.isHIT = true) (hyp : HITHyp2 S (d + 1))
    (E : ElimValid2 S Ψ Φ Γ d D ps M bs m) {t : Tm} (ht : HasTy0 S Ψ Φ Γ t (.data d ps))
    (hv : Valid2 S Ψ Φ Γ t t (.data d ps)) :
    Valid2 S Ψ Φ Γ (.elim d ps M bs t) (.elim d ps M bs t) (M.inst t) :=
  valid_elimH hW E.hD hH hyp (E.toElimPrem.elim_ty ht) (E.toElimPrem.elim_ty ht) E.dataV E.motiveV
    (fun c C b b' hc hb hb' => by rw [hb] at hb'; cases hb'; exact E.branchV c C b hc hb) hv E.boundaryV

/-- Congruence for a fixed valid eliminator's scrutinees. -/
theorem ElimValid2.congr (hH : D.isHIT = true) (hyp : HITHyp2 S (d + 1))
    (E : ElimValid2 S Ψ Φ Γ d D ps M bs m) {t t' : Tm}
    (he : EqTm0 S Ψ Φ Γ t t' (.data d ps)) (hv : Valid2 S Ψ Φ Γ t t' (.data d ps)) :
    Valid2 S Ψ Φ Γ (.elim d ps M bs t) (.elim d ps M bs t') (M.inst t) := by
  have hS := sigClosed_of_wfSig hW
  have hinst := HasTy0.inst_congr hS E.hP (presup hW he).1 (presup hW he).2 he
  refine valid_elimH hW E.hD hH hyp (E.toElimPrem.elim_ty (presup hW he).1)
    (HasTy0.conv (E.toElimPrem.elim_ty (presup hW he).2) (EqTm0.symm hinst))
    E.dataV E.motiveV ?_ hv E.boundaryV
  · intro c C b b' hc hb hb'
    rw [hb] at hb'
    cases hb'
    exact E.branchV c C b hc hb

end

end Model.Whnf
