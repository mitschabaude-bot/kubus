import Model.Whnf.Valid2ElimH32
import Model.Whnf.Valid2ElimHInv

/-! # Validity of higher inductive elimination and its congruence -/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

variable {S : Sig} (hW : WfSig S) {d : ℕ} {D : DataDecl} (hD : S[d]? = some (.data D))
include hW hD

/-- Elimination of related HIT elements is valid, from valid components and branch boundaries. -/
theorem valid_elimH (hH : D.isHIT = true) (hyp : HITHyp2 S (d + 1)) {Ψ : ℕ} {Φ : I} {Γ : Ctx} {ps ps' P P' bs bs' t t' : Tm} {m : ℕ}
    (hty : HasTy0 S Ψ Φ Γ (.elim d ps P bs t) (P.inst t)) (hty' : HasTy0 S Ψ Φ Γ (.elim d ps' P' bs' t') (P.inst t))
    (hps : Valid2 S Ψ Φ Γ (.data d ps) (.data d ps') (.univ D.level))
    (hM : Valid2 S Ψ Φ (.data d ps :: Γ) P P' (.univ m))
    (hbr : ∀ (c : ℕ) (C : Ctor) (b b' : Tm), D.ctors[c]? = some C → bs.toList[c]? = some b →
      bs'.toList[c]? = some b' → Valid2 S Ψ Φ Γ b b' (D.branchTy d c C ps P))
    (ht : Valid2 S Ψ Φ Γ t t' (.data d ps))
    (hbd : ∀ (c : ℕ) (C : Ctor) (b : Tm) (kb : ℕ) (ψ : I) (e : Tm), D.ctors[c]? = some C →
      bs.toList[c]? = some b → C.bnd[kb]? = some (ψ, e) →
      Valid2 S (Ψ + C.dims) (cof (Φ.ren (· + C.dims)) ψ) (D.branchCtx d C ps P Γ)
        (DataDecl.branchApp C b) (D.bndElim C ps bs e) (DataDecl.branchBody d c C ps P)) :
    Valid2 S Ψ Φ Γ (.elim d ps P bs t) (.elim d ps' P' bs' t') (P.inst t) := by
  obtain ⟨D0, m0, hE0, -⟩ := gen_elimP hty rfl
  obtain ⟨D1, m1, hE1, -⟩ := gen_elimP hty' rfl
  have e0 : D0 = D := by have := hE0.hD; rw [hD] at this; cases this; rfl
  have e1 : D1 = D := by have := hE1.hD; rw [hD] at this; cases this; rfl
  rw [e0] at hE0; rw [e1] at hE1
  have hpsL := valid_trans hW hps (valid_symm hW hps)
  have hML := valid_trans hW hM (valid_symm hW hM)
  have htL := valid_trans hW ht (valid_symm hW ht)
  have hbrL : ∀ (c : ℕ) (C : Ctor) (b b' : Tm), D.ctors[c]? = some C → bs.toList[c]? = some b →
      bs.toList[c]? = some b' → Valid2 S Ψ Φ Γ b b' (D.branchTy d c C ps P) := by
    intro cc C b b2 hC hb hb2
    rw [hb] at hb2; cases hb2
    have hcl : cc < D.ctors.length := (List.getElem?_eq_some_iff.1 hC).1
    obtain ⟨b', hb'⟩ : ∃ b, bs'.toList[cc]? = some b := ⟨_, List.getElem?_eq_getElem (by rw [hE1.hlen]; exact hcl)⟩
    have h := hbr cc C b b' hC hb hb'
    exact valid_trans hW h (valid_symm hW h)
  intro k c
  have hRL : ElimRelH S d D k (c.L ps) (P.subst (Tm.up c.γ) c.σ.τ) (c.L bs) (c.L ps) (P.subst (Tm.up c.γ) c.σ.τ)
      (c.L bs) := elimRelH_of hW hD hty hty hpsL hML hbrL (c.diagL hW)
  have hER := elimRelH_of hW hD hty hty' hps hM hbr c
  have hP : HasTy S k .one [] (.data d (c.L ps)) (.univ D.level) := c.ty hW hE0.hdata
  have hPP : RT2 S k (.data d (c.L ps)) (.data d (c.L ps)) := hpsL.ty hW (c.diagL hW)
  have hx : RE2 S k (.data d (c.L ps)) (c.L t) (c.R t') := (ht k c).2
  have hpc : (c.L ps).closedB 0 k = true := by
    have := closed_of_ty hW hP; simpa [Tm.closedB] using this
  have hx' : RE2 S k (.data d ((c.L ps).isub (ISub.id k))) (c.L t) (c.R t') := by
    rw [isub_id_of_closed hpc]; exact hx
  obtain ⟨-, hdr⟩ := (RE2_dataLit_iff hW hD hP (ISub.id k)).1 hx'
  have HB : ElimBndRel2 S d D k (c.L ps) (P.subst (Tm.up c.γ) c.σ.τ) (c.L bs) :=
    elimBndRel_of hW hD hE0.hps hE0.hpt hE0.hbs hE0.hlen
      (fun cc C b hc hb => hbrL cc C b b hc hb hb) hbd c
  have T := (elim_DR2H hW hD hH hyp hP hPP hRL HB hdr).1 (ISub.id k) rfl rfl _ _ _ hER
  have hcl := closed_of_ty hW (c.ty hW hty)
  have hcl' := closed_of_ty hW (c.tyR hW hty')
  simp only [CSub2.L, CSub2.R, Tm.subst, Tm.closedB, Bool.and_eq_true] at hcl hcl'
  rw [isub_id_of_closed hpc, isub_id_of_closed hcl.1.1.2, isub_id_of_closed hcl.1.2,
    isub_id_of_closed hcl'.1.1.1, isub_id_of_closed hcl'.1.1.2, isub_id_of_closed hcl'.1.2] at T
  refine ⟨?_, ?_⟩
  · have := hML.ty hW (c.ext hW (.data d ps) (c.L t) (c.R t) (htL k c).2
      (CSub2.tyRob_of hW (fun k c => hpsL.tySelf hW c) _))
    show RT2 S k ((P.inst t).subst c.γ c.σ.τ) ((P.inst t).subst c.γ' c.σ'.τ)
    rw [inst_subst_consT, inst_subst_consT]
    exact this
  · show RE2 S k ((P.inst t).subst c.γ c.σ.τ) _ _
    rw [inst_subst]
    exact T

/-- Elimination congruence recovers the left branch boundary premises by typing inversion. -/
theorem valid_elimEqH (hH : D.isHIT = true) (hyp : HITHyp2 S (d + 1))
    {Ψ : ℕ} {Φ : I} {Γ : Ctx} {ps ps' P P' bs bs' t t' T : Tm} {m : ℕ}
    (hinv : ElimInv2 S Ψ Φ Γ d ps P bs t T)
    (hty : HasTy0 S Ψ Φ Γ (.elim d ps P bs t) (P.inst t))
    (hty' : HasTy0 S Ψ Φ Γ (.elim d ps' P' bs' t') (P.inst t))
    (hps : Valid2 S Ψ Φ Γ (.data d ps) (.data d ps') (.univ D.level))
    (hM : Valid2 S Ψ Φ (.data d ps :: Γ) P P' (.univ m))
    (hbr : ∀ (c : ℕ) (C : Ctor) (b b' : Tm), D.ctors[c]? = some C → bs.toList[c]? = some b →
      bs'.toList[c]? = some b' → Valid2 S Ψ Φ Γ b b' (D.branchTy d c C ps P))
    (ht : Valid2 S Ψ Φ Γ t t' (.data d ps)) :
    Valid2 S Ψ Φ Γ (.elim d ps P bs t) (.elim d ps' P' bs' t') (P.inst t) := by
  obtain ⟨D0, _, hd, _, _, _, _, _, _, _, _, _, hbd, _, _⟩ := hinv
  rw [hD] at hd
  cases hd
  exact valid_elimH hW hD hH hyp hty hty' hps hM hbr ht hbd

end

end Model.Whnf
