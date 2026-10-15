import Model.Whnf.Kan2DataHITTC

/-!
# Transport along related lines: symmetry, and lines related to argument lines

`KanT2.flip`: transport along related lines, with the lines exchanged. `argLine_kanT2`: transport along an
argument line (at self-related earlier arguments) and any line related to it, from the Kan property of the
argument type's code.
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

attribute [local instance] Classical.propDecidable

variable {S : Sig} {k k' k'' : ℕ}

/-- Transport along related lines, with the lines exchanged. -/
theorem KanT2.flip (hW : WfSig S) {A A' : Tm} (h : KanT2 S k A' A) : KanT2 S k A A' := by
  intro hLR φ φ' a a' hLC hty hty' heq h12 h21 ha
  obtain ⟨l, ⟨hA, -, -, -⟩, -⟩ := gen_transpF (spec_to_minimal hW hty) rfl
  obtain ⟨l', ⟨hA', -, -, -⟩, -⟩ := gen_transpF (spec_to_minimal hW hty') rfl
  have hAc : A.closedB 0 (k + 1) = true := closed_ty hA
  have hA'c : A'.closedB 0 (k + 1) = true := closed_ty hA'
  have hXA : ∀ {k3 : ℕ} (θ : ISub k3 (k + 1)), TyCode k3 (semK S k3 (A.isub θ)) := fun θ =>
    tyCode_of_univ hW (HasTy.isubS hW (minimal_to_spec hA) θ)
  have hXA' : ∀ {k3 : ℕ} (θ : ISub k3 (k + 1)), TyCode k3 (semK S k3 (A'.isub θ)) := fun θ =>
    tyCode_of_univ hW (HasTy.isubS hW (minimal_to_spec hA') θ)
  have hLR' : LineRob S k A' A := fun k3 τ r r' hr hr' hE =>
    RT2.symm hW (hXA _) (hLR k3 τ r' r hr' hr (I_eq_symm hE))
  have hLC' : LineConst S k A' φ' := by
    intro k3 τ r hr hh
    have hs := I.scoped_subst (gen_transpF (spec_to_minimal hW hty') rfl).choose_spec.1.2.1 τ.sc
    have hφ : (ival (idEnv k3) (φ.subst τ.τ)).holds := by
      have hs0 := I.scoped_subst (gen_transpF (spec_to_minimal hW hty) rfl).choose_spec.1.2.1 τ.sc
      exact (holds_iff_entails hs0).2 (ent_trans ((holds_iff_entails hs).1 hh) (ent_subst h21 _))
    have r1 := hLR' k3 τ r r hr hr (I_eq_refl _)
    have r2 := hLC k3 τ r hr hφ
    have r3 := hLR k3 τ .zero .zero trivial trivial (I_eq_refl _)
    exact RT2.trans hW (hXA' _) r1 (RT2.trans hW (hXA _) r2 r3)
  have e1 : RT2 S k (A.dinst .one) (A'.dinst .one) := by
    have := hLR k (ISub.id k) .one .one trivial trivial (I_eq_refl _)
    rwa [isub_cons_id_of_closed hAc, isub_cons_id_of_closed hA'c] at this
  have e0 : RT2 S k (A.dinst .zero) (A'.dinst .zero) := by
    have := hLR k (ISub.id k) .zero .zero trivial trivial (I_eq_refl _)
    rwa [isub_cons_id_of_closed hAc, isub_cons_id_of_closed hA'c] at this
  have hX1 : TyCode k (semK S k (A.dinst .one)) := by
    have := hXA (ISub.cons .one trivial (ISub.id k)); rwa [isub_cons_id_of_closed hAc] at this
  have tyB : ∀ {k4 : ℕ} {X Z : Tm}, RT2 S k4 X Z → TyEq S k4 X Z := fun h => (Comp2_ty_base h).2.2.2.2.2
  have R := h hLR' φ' φ a' a hLC' (hty'.tyConv (tyB e1)) (hty.tyConv (tyB e1)) (heq.symm.tyConv (tyB e1)) h21 h12
    (RE2.conv hW e0 (RE2.symm hW (RT2.refl hW (RE2.tyCode hW ha) e0) ha))
  have e1' := RT2.symm hW hX1 e1
  exact RE2.symm hW (RT2.refl hW hX1 e1) (RE2.conv hW e1' R)

section wrap
variable (hW : WfSig S) {d : ℕ} {D : DataDecl} (hD : S[d]? = some (.data D))
include hW hD

/-- Transport along an argument line at self-related earlier arguments, against any related line. -/
theorem argLine_kanT2 {n' : ℕ} {P1 L2 : Tm} (hP1 : HasTy S (n' + 1) .one [] (.data d P1) (.univ D.level))
    (hP1P1 : RT2 S (n' + 1) (.data d P1) (.data d P1))

    {c : ℕ} {C : Ctor} (hC : D.ctors[c]? = some C) {A : List Tm}
    (hAl : A.length < C.args.length) (hrr : C.isRec A.length = false)
    (hrel : ∀ i (hi : i < A.length), RE2 S (n' + 1) ((C.argTy d D.params.length i).substList ((A.take i).reverse ++
      P1.toList.reverse)) (A.getD i .abort) (A.getD i .abort))
    (hL2 : RT2 S (n' + 1) ((C.argTy d D.params.length A.length).substList (A.reverse ++ P1.toList.reverse)) L2) :
    KanT2 S n' ((C.argTy d D.params.length A.length).substList (A.reverse ++ P1.toList.reverse)) L2 := by
  have hdD := dataD_eq hW hD
  have hP1c := data_closed hW hD hP1
  have hPl : IsList P1 := by
    have := (dataLit_rel hW hD hP1 hP1P1 (ISub.id (n' + 1))).2.2.2.2.2.1; rwa [isub_id_of_closed hP1c] at this
  have hplen : P1.toList.length = D.params.length := by
    have := data_len_of hW (⟨_, .inl hP1⟩ : IsTyK S (n' + 1) (.data d P1)); rwa [hdD] at this
  have hRR' := (dataLit_rel hW hD hP1 hP1P1 (ISub.id (n' + 1))).1
  rw [isub_id_of_closed hP1c] at hRR'
  have hRsem := semK_dataQ hW hD hP1 hP1P1 (ISub.id (n' + 1))
  rw [isub_id_of_closed hP1c] at hRsem
  have hA := argTy_code_rel hW hD hP1 (ISub.id (n' + 1)) hRR' hRsem hP1c hP1c hC (A' := A) rfl
    (fun i hi hi' hri => by
      have h := hrel i hi
      rwa [argTy_rec_inst hri hPl hplen (by simp; omega), getD_eq_get' hi] at h)
    (fun i hi hi' hri => by
      have h := hrel i hi
      rwa [getD_eq_get' hi] at h)
    hAl hrr
  have hb := Comp2_ty_base hA.1
  have hA2 := (Comp2_ty_iff hb.1 hb.2.2.2.1).2 hL2
  exact hA.2.2 n' (Hom.id (n' + 1)) _ _ hA2

end wrap

end

end Model.Whnf
