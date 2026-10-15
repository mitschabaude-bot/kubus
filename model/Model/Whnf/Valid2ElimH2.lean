import Model.Whnf.Valid2ElimH1

/-!
# Kan evidence for higher inductive eliminators

The motive is valid in a universe at arguments related in the declared data type. Its code's Kan
operations therefore follow at those arguments, including the lines used by `elimHcomp`.
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

variable {S : Sig} {k : ℕ}

/-- Related eliminator components with the motive's relation-carried Kan evidence. -/
structure ElimRelH (S : Sig) (d : ℕ) (D : DataDecl) (K : ℕ) (P M bs Q M' bs' : Tm)
    extends ElimRel S d D K P M bs Q M' bs' : Prop where
  kan : ∀ k1 (ρ : ISub k1 K) (x x' : Tm), RE2 S k1 (.data d (P.isub ρ)) x x' →
    KanP2 S k1 (semK S k1 ((M.isub ρ).inst x))

variable (hW : WfSig S)
include hW

/-- Related eliminator components inherit Kan from the motive's universe premise. -/
theorem elimRelH_of {d : ℕ} {D : DataDecl} (hD : S[d]? = some (.data D))
    {Ψ : ℕ} {Φ : I} {Γ : Ctx} {ps ps' P P' bs bs' t t' T T' : Tm} {m : ℕ}
    (hty : HasTy0 S Ψ Φ Γ (.elim d ps P bs t) T)
    (hty' : HasTy0 S Ψ Φ Γ (.elim d ps' P' bs' t') T')
    (hps : Valid2 S Ψ Φ Γ (.data d ps) (.data d ps') (.univ D.level))
    (hM : Valid2 S Ψ Φ (.data d ps :: Γ) P P' (.univ m))
    (hbr : ∀ (c : ℕ) (C : Ctor) (b b' : Tm), D.ctors[c]? = some C → bs.toList[c]? = some b →
      bs'.toList[c]? = some b' → Valid2 S Ψ Φ Γ b b' (D.branchTy d c C ps P))
    (c : CSub2 S Ψ Φ Γ k) :
    ElimRelH S d D k (c.L ps) (P.subst (Tm.up c.γ) c.σ.τ) (c.L bs)
      (c.R ps') (P'.subst (Tm.up c.γ') c.σ'.τ) (c.R bs') :=
  ⟨elimRel_of hW hD hty hty' hps hM hbr c,
    fun _ ρ _ _ hx => hps.codKan hW hM c ρ hx⟩

/-- Compositions in the motive at related arguments. -/
theorem ElimRelH.motH {d : ℕ} {D : DataDecl} {K : ℕ} {P M bs Q M' bs' : Tm}
    (H : ElimRelH S d D K P M bs Q M' bs') (ρ : ISub k K) {x x' : Tm}
    (hx : RE2 S k (.data d (P.isub ρ)) x x') :
    KanH2 S k ((M.isub ρ).inst x) ((M'.isub ρ).inst x') :=
  (H.kan k ρ x x' hx).1 k (Hom.id k) _ _ (H.mot k ρ x x' hx)

/-- Transport in the motive along related argument lines. -/
theorem ElimRelH.motT {d : ℕ} {D : DataDecl} {K : ℕ} {P M bs Q M' bs' : Tm}
    (H : ElimRelH S d D K P M bs Q M' bs') (ρ : ISub (k + 1) K) {x x' : Tm}
    (hx : RE2 S (k + 1) (.data d (P.isub ρ)) x x') :
    KanT2 S k ((M.isub ρ).inst x) ((M'.isub ρ).inst x') :=
  (H.kan (k + 1) ρ x x' hx).2 k (Hom.id (k + 1)) _ _ (H.mot (k + 1) ρ x x' hx)


/-- A constructor normal form gives a typed reduct of its elimination. -/
theorem elim_reductH {d : ℕ} {D : DataDecl} (hD : S[d]? = some (.data D))
    {ps M bs : Tm} {m : ℕ} (hE : ElimPrem S k .one [] d D ps M bs m) {x : Tm}
    (hx : HasTy S k .one [] x (.data d ps)) {c : ℕ} {C : Ctor} (hC : D.ctors[c]? = some C)
    {qs : Tm} {X : List Tm} {rs : List I}
    (hw : RedE S k (.data d ps) x (.con d c qs (Tm.ofList X) rs))
    (hn : firstBnd C.bnd rs = none) :
    Red S (.elim d ps M bs x)
      (Tm.papps (Tm.apps (bs.toList.getD c .abort) (X ++ ihsOf d C ps M bs X)) rs) ∧
    EqTm S k .one [] (.elim d ps M bs x)
      (Tm.papps (Tm.apps (bs.toList.getD c .abort) (X ++ ihsOf d C ps M bs X)) rs) (M.inst x) := by
  have hS := sigClosed_of_wfSig hW
  have hc : c < bs.toList.length := by
    rw [hE.hlen]
    exact (List.getElem?_eq_some_iff.1 hC).1
  have hb : bs.toList[c]? = some (bs.toList.getD c .abort) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hc]
    rfl
  refine ⟨(red_elim_scrut hw.1.1).trans (.step (step_elimConH hD hC hb hn) (.refl _)), ?_⟩
  obtain ⟨htele, -, -, -, -, -, hcp, econ, -⟩ :=
    con_inv hW hD hC (HasTy.eqR hw.2) (minimal_to_spec hE.hdata)
  have ex := hw.2.trans econ
  have hx0 := spec_to_minimal hW hx
  have hcp0 := spec_to_minimal hW hcp
  have e1 := hE.elim_congr hS hx0 hcp0 (spec_to_minimal_eq hW ex)
  have e2 := EqTm.elimCon (T := M.inst (.con d c ps (Tm.ofList X) rs)) hD hC hb hE.hps
    (by rw [toList_ofList]) hE.hbs (toFull_tele htele) (minimal_to_spec (hE.elim_ty hcp0))
  rw [toList_ofList] at e2
  have eP := HasTy0.inst_congr hS hE.hP hcp0 hx0 (EqTm0.symm (spec_to_minimal_eq hW ex))
  exact (minimal_to_spec_eq e1).trans (e2.tyConv (.inr ⟨m, minimal_to_spec_eq eP⟩))

/-- The contractum of elimination at a formal composition. -/
abbrev elimHcompTm (d : ℕ) (ps M bs : Tm) (φ : I) (u a : Tm) : Tm :=
  Tm.comp (M.subst (fun | 0 => Tm.hfill (.data d ps) φ u a | j + 1 => .var j) (fun i => .var (i + 1))) φ
    (.elim d ps.dshift M.dshift bs.dshift u) (.elim d ps M bs a)

/-- A formal composition normal form gives a typed reduct of its elimination. -/
theorem elim_hcomp_reductH {d : ℕ} {D : DataDecl} (hD : S[d]? = some (.data D)) (hH : D.isHIT = true)
    {ps M bs : Tm} {m : ℕ} (hE : ElimPrem S k .one [] d D ps M bs m) {x : Tm}
    (hx : HasTy S k .one [] x (.data d ps)) {qs u a : Tm} {φ : I}
    (hw : RedE S k (.data d ps) x (.hcomp (.data d qs) φ u a)) (hn : ¬ I.Entails .one φ) :
    Red S (.elim d ps M bs x) (elimHcompTm d ps M bs φ u a) ∧
    EqTm S k .one [] (.elim d ps M bs x) (elimHcompTm d ps M bs φ u a) (M.inst x) := by
  have hS := sigClosed_of_wfSig hW
  refine ⟨(red_elim_scrut hw.1.1).trans (.step (step_elimHcompH hD hH hn) (.refl _)), ?_⟩
  have hh0 := spec_to_minimal hW (HasTy.eqR hw.2)
  have hx0 := spec_to_minimal hW hx
  have e1 := hE.elim_congr hS hx0 hh0 (spec_to_minimal_eq hW hw.2)
  have hp := (hcomp_data_retype hW (HasTy.eqR hw.2) (minimal_to_spec hE.hdata)).1
  have e2 := EqTm.elimHcomp hD hH hp (minimal_to_spec (hE.elim_ty hh0))
  have eP := HasTy0.inst_congr hS hE.hP hh0 hx0 (EqTm0.symm (spec_to_minimal_eq hW hw.2))
  exact (minimal_to_spec_eq e1).trans (e2.tyConv (.inr ⟨m, minimal_to_spec_eq eP⟩))

end

end Model.Whnf
