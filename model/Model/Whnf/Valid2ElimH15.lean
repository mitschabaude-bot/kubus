import Model.Whnf.Valid2ElimH14

/-!
# Related composition contracta of higher inductive eliminators

The recursive eliminations of the tubes, bases and boundaries compose in the motive along a
computable filler line. The motive's universe premise supplies its Kan operations.
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

variable {S : Sig} {k : ℕ} (hW : WfSig S)
include hW

/-- Compose related recursive eliminations along related filler lines. -/
theorem elimComp_relH {d : ℕ} {D : DataDecl} {K : ℕ} {P M bs Q M' bs' : Tm}
    (HL : ElimRelH S d D K P M bs P M bs) (H : ElimRelH S d D K P M bs Q M' bs')
    (ρ : ISub k K) {F F' u u' a a' : Tm} {φ φ' : I}
    (hF : HasTy S (k + 1) .one [] F (Tm.data d (P.isub ρ)).dshift)
    (hFF : ∀ k' (σ σ' : ISub k' (k + 1)), σ.tail = σ'.tail → I.Eq (σ.τ 0) (σ'.τ 0) →
      RE2 S k' (.data d (P.isub (ρ.comp σ.tail))) (F.isub σ) (F'.isub σ'))
    (hFL : ∀ k' (σ σ' : ISub k' (k + 1)), σ.tail = σ'.tail → I.Eq (σ.τ 0) (σ'.τ 0) →
      RE2 S k' (.data d (P.isub (ρ.comp σ.tail))) (F.isub σ) (F.isub σ'))
    (hface : ∀ k' (σ : ISub k' k) (r : I) (hr : r.Scoped k'),
      (ival (idEnv k') (φ.subst σ.τ)).holds →
      RE2 S k' (.data d (P.isub (ρ.comp σ))) (F.isub (ISub.cons r hr σ)) ((u.isub σ.up).dinst r))
    (hzero : ∀ k' (σ : ISub k' k),
      RE2 S k' (.data d (P.isub (ρ.comp σ))) (F.isub (ISub.cons .zero trivial σ)) (a.isub σ))
    (hb : HcompBnd2 S k (.data d (P.isub ρ)) φ u a)
    (huE : ∀ k' (σ : ISub k' k) (r r' : I), r.Scoped k' → r'.Scoped k' → I.Eq r r' →
      (ival (idEnv k') (φ.subst σ.τ)).holds →
      RE2 S k' ((M.isub (ρ.comp σ)).inst ((u.isub σ.up).dinst r))
        (((Tm.elim d (P.isub ρ).dshift (M.isub ρ).dshift (bs.isub ρ).dshift u).isub σ.up).dinst r)
        (((Tm.elim d (Q.isub ρ).dshift (M'.isub ρ).dshift (bs'.isub ρ).dshift u').isub σ.up).dinst r'))
    (haE : RE2 S k ((M.isub ρ).inst a)
      (.elim d (P.isub ρ) (M.isub ρ) (bs.isub ρ) a)
      (.elim d (Q.isub ρ) (M'.isub ρ) (bs'.isub ρ) a'))
    (hbE : ∀ k' (σ : ISub k' k), (ival (idEnv k') (φ.subst σ.τ)).holds →
      RE2 S k' ((M.isub (ρ.comp σ)).inst ((u.isub σ.up).dinst .zero))
        (((Tm.elim d (P.isub ρ).dshift (M.isub ρ).dshift (bs.isub ρ).dshift u).isub σ.up).dinst .zero)
        ((Tm.elim d (P.isub ρ) (M.isub ρ) (bs.isub ρ) a).isub σ))
    (ht : HasTy S k .one [] (Tm.comp (motiveLine (M.isub ρ) F) φ
      (.elim d (P.isub ρ).dshift (M.isub ρ).dshift (bs.isub ρ).dshift u)
      (.elim d (P.isub ρ) (M.isub ρ) (bs.isub ρ) a)) ((motiveLine (M.isub ρ) F).dinst .one))
    (ht' : HasTy S k .one [] (Tm.comp (motiveLine (M'.isub ρ) F') φ'
      (.elim d (Q.isub ρ).dshift (M'.isub ρ).dshift (bs'.isub ρ).dshift u')
      (.elim d (Q.isub ρ) (M'.isub ρ) (bs'.isub ρ) a')) ((motiveLine (M.isub ρ) F).dinst .one))
    (h12 : I.Entails φ φ') (h21 : I.Entails φ' φ) :
    RE2 S k ((motiveLine (M.isub ρ) F).dinst .one)
      (Tm.comp (motiveLine (M.isub ρ) F) φ
        (.elim d (P.isub ρ).dshift (M.isub ρ).dshift (bs.isub ρ).dshift u)
        (.elim d (P.isub ρ) (M.isub ρ) (bs.isub ρ) a))
      (Tm.comp (motiveLine (M'.isub ρ) F') φ'
        (.elim d (Q.isub ρ).dshift (M'.isub ρ).dshift (bs'.isub ρ).dshift u')
        (.elim d (Q.isub ρ) (M'.isub ρ) (bs'.isub ρ) a')) := by
  obtain ⟨m, hE⟩ := HL.tyL k ρ
  have hC : HasTy S (k + 1) .one [] (motiveLine (M.isub ρ) F) (.univ m) := by
    rw [motiveLine_eq]
    exact minimal_to_spec (HasTy0.subst (sigClosed_of_wfSig hW)
      (HasTy0.dwk (sigClosed_of_wfSig hW) hE.hP) (spec_to_minimal hW hF))
  have hFc := closed_of_ty hW hF
  have hFF0 := hFL (k + 1) (ISub.id (k + 1)) (ISub.id (k + 1)) rfl (I_eq_refl _)
  rw [isub_id_of_closed hFc] at hFF0
  have ei : (ISub.id (k + 1)).tail = ISub.wk k := by
    ext i
    simp only [ISub.id, ISub.tail, ISub.wk]
    by_cases hi : i < k
    · simp [hi, show i + 1 < k + 1 by omega]
    · simp [hi, show ¬ i + 1 < k + 1 by omega]
  rw [ei] at hFF0
  have hK := HL.lineKan hW ρ (by
    change RE2 S (k + 1) (.data d ((P.isub ρ).isub (ISub.wk k))) F F
    rw [Tm.isub_isub]
    exact hFF0)
  have hCt := fun {k'} (θ : ISub k' (k + 1)) => tyCode_of_univ hW (HasTy.isubS hW hC θ)
  have faceT : ∀ k' (σ : ISub k' k) r (hr : r.Scoped k'), (ival (idEnv k') (φ.subst σ.τ)).holds →
      RT2 S k' ((motiveLine (M.isub ρ) F).isub (ISub.cons r hr σ))
        ((M.isub (ρ.comp σ)).inst ((u.isub σ.up).dinst r)) := by
    intro k' σ r hr hh
    rw [motiveLine_isub, Tm.isub_isub]
    exact HL.mot k' (ρ.comp σ) _ _ (hface k' σ r hr hh)
  have hac : a.closedB 0 k = true := by
    have := closed_of_ty hW (RE2.typed haE).1
    simp only [Tm.closedB, Bool.and_eq_true] at this
    exact this.2
  have hC0 : HasTy S k .one [] ((motiveLine (M.isub ρ) F).dinst .zero) (.univ m) :=
    minimal_to_spec (HasTy0.dsubst (Φ := .one) (Γ := []) (sigClosed_of_wfSig hW) (spec_to_minimal hW hC) (r := .zero) trivial)
  have zeroT : RT2 S k ((motiveLine (M.isub ρ) F).dinst .zero) ((M.isub ρ).inst a) := by
    have R := hzero k (ISub.id k)
    rw [ISub.comp_id, isub_cons_id_of_closed hFc .zero trivial,
      isub_id_of_closed hac] at R
    simpa only [motiveLine_eq, dshift_inst_dinst] using HL.mot k ρ _ _ R
  refine comp2r_code hW hC hK (H.lineRob hW ρ hFF) (HL.lineRob hW ρ hFL) ht ht' h12 h21 ?_
    (RE2.conv hW (RT2.symm hW (tyCode_of_univ hW hC0) zeroT) haE) ?_ ?_
  · intro k' σ r r' hr hr' he hh
    exact RE2.conv hW (RT2.symm hW (hCt _) (faceT k' σ r hr hh)) (huE k' σ r r' hr hr' he hh)
  · intro k' σ hh
    have rb := hbE k' σ hh
    have ba := RE2.isub hW haE σ
    rw [isub_inst, Tm.isub_isub] at ba
    have T := HL.mot k' (ρ.comp σ) _ _ (by simpa only [data_isub_comp] using hb k' σ hh)
    have R := RE2.trans hW (RT2.refl hW (RE2.tyCode hW rb) T) rb
      (RE2.conv hW (RT2.symm hW (RE2.tyCode hW rb) T) ba)
    exact RE2.conv hW (RT2.symm hW (hCt _) (faceT k' σ .zero trivial hh)) R
  · intro k' σ hh
    have rb := hbE k' σ hh
    have T := HL.mot k' (ρ.comp σ) _ _ (by simpa only [data_isub_comp] using hb k' σ hh)
    have R := RE2.trans hW (RT2.refl hW (RE2.tyCode hW rb) T) (RE2.symm hW (RT2.refl hW (RE2.tyCode hW rb) T) rb)
      (huE k' σ .zero .zero trivial trivial (I_eq_refl _) hh)
    exact RE2.conv hW (RT2.symm hW (hCt _) (faceT k' σ .zero trivial hh)) R

end

end Model.Whnf
