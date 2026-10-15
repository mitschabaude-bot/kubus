import Model.Whnf.Valid2ElimH10

/-!
# The closed boundary premise of higher inductive elimination

Validity in the branch context supplies boundary agreement at every related closing instance.
The premise refers to the declared parameter annotation and computable recursive eliminations.
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

variable {S : Sig} {k : ℕ}

/-- Branch boundary agreement, uniformly in restrictions and computable constructor arguments. -/
def ElimBndRel2 (S : Sig) (d : ℕ) (D : DataDecl) (K : ℕ) (P M bs : Tm) : Prop :=
  ∀ {k : ℕ} (ρ : ISub k K) {c : ℕ} {C : Ctor} {kb : ℕ} {ψ : I} {e : Tm},
    D.ctors[c]? = some C → C.bnd[kb]? = some (ψ, e) →
    ∀ (X : List Tm) (rs : List I), X.length = C.args.length → rs.length = C.dims →
    (∀ r ∈ rs, r.Scoped k) → I.Entails .one (Ctor.cofAt ψ rs) →
    (∀ i (_hi : i < C.args.length), RE2 S k ((C.argTy d D.params.length i).substList
      ((X.take i).reverse ++ (P.isub ρ).toList.reverse)) (X.getD i .abort) (X.getD i .abort)) →
    (∀ i, i ∈ C.recPos → RE2 S k ((M.isub ρ).inst (X.getD i .abort))
      (.elim d (P.isub ρ) (M.isub ρ) (bs.isub ρ) (X.getD i .abort))
      (.elim d (P.isub ρ) (M.isub ρ) (bs.isub ρ) (X.getD i .abort))) →
    RE2 S k ((M.isub ρ).inst (.con d c (P.isub ρ) (Tm.ofList X) rs))
      (Tm.papps (ecTm d C c (P.isub ρ) (M.isub ρ) (bs.isub ρ) X) rs)
      (bndInterp2 d D C (P.isub ρ) (M.isub ρ) (bs.isub ρ) X rs e)

variable (hW : WfSig S)
include hW

/-- The boundary equation premise closes to branch agreement in the constructor algebra. -/
theorem elimBndRel_of {d : ℕ} {D : DataDecl} (hD : S[d]? = some (.data D))
    {Ψ : ℕ} {Φ : I} {Γ : Ctx} {ps M bs : Tm} (hps : IsList ps)
    (hTele : HasTele0 S Ψ Φ Γ ps D.params []) (hbs : IsList bs) (hlen : bs.toList.length = D.ctors.length)
    (hbr : ∀ (c : ℕ) (C : Ctor) (b : Tm), D.ctors[c]? = some C → bs.toList[c]? = some b →
      Valid2 S Ψ Φ Γ b b (D.branchTy d c C ps M))
    (hbd : ∀ (c : ℕ) (C : Ctor) (b : Tm) (kb : ℕ) (ψ : I) (e : Tm), D.ctors[c]? = some C →
      bs.toList[c]? = some b → C.bnd[kb]? = some (ψ, e) →
      Valid2 S (Ψ + C.dims) (cof (Φ.ren (· + C.dims)) ψ) (D.branchCtx d C ps M Γ)
        (DataDecl.branchApp C b) (D.bndElim C ps bs e) (DataDecl.branchBody d c C ps M))
    (cσ : CSub2 S Ψ Φ Γ k) :
    ElimBndRel2 S d D k (cσ.L ps) (M.subst (Tm.up cσ.γ) cσ.σ.τ) (cσ.L bs) := by
  intro k' ρ c C kb ψ e hC hb X rs hX hrs hsc hh ha hi
  let cρ := (cσ.restr hW ρ).diagL hW
  have eP : cρ.L ps = (cσ.L ps).isub ρ := cσ.restr_L hW ρ ps
  have eM : M.subst (Tm.up cρ.γ) cρ.σ.τ = (M.subst (Tm.up cσ.γ) cσ.σ.τ).isub ρ := cσ.upL_restr hW ρ M
  have ebs : cρ.L bs = (cσ.L bs).isub ρ := cσ.restr_L hW ρ bs
  have eRP : cρ.R ps = cρ.L ps := rfl
  have eRM : M.subst (Tm.up cρ.γ') cρ.σ'.τ = M.subst (Tm.up cρ.γ) cρ.σ.τ := rfl
  have eRbs : cρ.R bs = cρ.L bs := rfl
  have eγ : cρ.γ' = cρ.γ := rfl
  have eσ : cρ.σ' = cρ.σ := rfl
  have hc : c < bs.toList.length := by rw [hlen]; exact (List.getElem?_eq_some_iff.1 hC).1
  let b := bs.toList.getD c .abort
  have hbb : bs.toList[c]? = some b := by
    change bs.toList[c]? = some (bs.toList.getD c .abort)
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hc]
    rfl
  obtain ⟨hψ, hec, hes, -⟩ := ((hW.2 d D hD).2.2 c C hC).2.1 kb ψ e hb
  have hpl := Meta.tele_length hTele
  have R := valid_branchBnd_rel2 hW hD hC hps hpl (hbr c C b hC hbb) hψ (hbd c C b kb ψ e hC hbb hb)
    cρ X X hX hX (by simpa only [eP] using ha) (by simpa only [eRP, eRM, eRbs, eP, eM, ebs] using hi)
    rs rs hrs (ieqL_iff.2 (forall2_ieq_refl _)) hsc hsc hh
  simp only [eRP, eRM, eRbs, eγ, eσ] at R
  rw [bndElim_interp_inst2 hps hpl hbs X rs hX hrs cρ.γ cρ.σ.τ (sizeOf e + 1) e (by omega)
    hes (by rwa [hpl])] at R
  have eb : cρ.L b = (cρ.L bs).toList.getD c .abort := by
    simpa only [CSub2.L, b, toList_subst hbs] using (getD_map_abort bs.toList c cρ.γ cρ.σ.τ).symm
  rw [eb, eP, eM, ebs] at R
  have eP' : ps.subst cρ.γ cρ.σ.τ = (cσ.L ps).isub ρ := eP
  have ebs' : bs.subst cρ.γ cρ.σ.τ = (cσ.L bs).isub ρ := ebs
  rw [eP', ebs'] at R
  exact R

end

end Model.Whnf
