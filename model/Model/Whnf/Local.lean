import Model.Canon.ProjHcomp

/-!
# Judgmental equality under a face, from its restrictions
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

variable {S : Sig} (hW : WfSig S)
include hW

/-- Two terms over a face are equal if all their restrictions where the face holds are. -/
theorem eq_of_restr {k : ℕ} {φ : I} (hφs : φ.Scoped k) {X t t' : Tm} {l : ℕ}
    (hX : HasTy S k (cof .one φ) [] X (.univ l) ∨ X = .univ l) (ht : HasTy S k (cof .one φ) [] t X)
    (ht' : HasTy S k (cof .one φ) [] t' X)
    (h : ∀ k' (σ : ISub k' k), (ival (idEnv k') (φ.subst σ.τ)).holds →
      EqTm S k' .one [] (t.isub σ) (t'.isub σ) (X.isub σ)) :
    EqTm S k (cof .one φ) [] t t' X := by
  have hS := sigClosed_of_wfSig hW
  have ht0 := spec_to_minimal hW ht
  have ht'0 := spec_to_minimal hW ht'
  have hΦs : (cof .one φ).Scoped k := ⟨trivial, hφs⟩
  refine minimal_to_spec_eq (eq_local_faces ht0 ht'0 fun α hα => ?_)
  have hcα := faces_consistent hα
  have hsc := faces_scoped hΦs α hα
  have hsα : (I.ofFace α).Scoped k := scoped_ofFace hsc
  have hΞs : (cof (cof .one φ) (I.ofFace α)).Scoped k := ⟨hΦs, hsα⟩
  have hτ : ∀ i < k, (faceSub α i).Scoped k := fun i hi => by
    rcases faceSub_cases α i with ⟨e, _, h⟩ | ⟨_, h⟩
    · rw [h]; cases e <;> trivial
    · rw [h]; exact hi
  set ρ := ISub.ofFun k (faceSub α) hτ with hρ
  have hface : (ival (idEnv k) (φ.subst ρ.τ)).holds := by
    rw [holds_iff_entails (I.scoped_subst hφs ρ.sc)]
    have h1 : I.Entails (I.ofFace α) φ := ent_trans (ofFace_ent hα) (ent_and_right _ _)
    have h2 := ent_trans (ent_ofFace_faceSub hcα) (ent_subst h1 (faceSub α))
    have e3 : φ.subst (faceSub α) = φ.subst ρ.τ :=
      I_subst_congr_scoped (fun i hi => by show faceSub α i = (if i < k then faceSub α i else .zero); rw [if_pos hi]) hφs
    rwa [e3] at h2
  have e := spec_to_minimal_eq hW (h k ρ hface)
  rw [isub_ofFun (closed_ty ht0), isub_ofFun (closed_ty ht'0)] at e
  have eΞ := EqTm0.restrict hΞs (ent_one _) e
  rcases hX with hX | rfl
  · have hX0 := spec_to_minimal hW hX
    rw [isub_ofFun (closed_ty hX0)] at eΞ
    have hXΞ := HasTy0.restrict hΞs (ent_and_left _ _) hX0
    have e_t := face_all hW (.inl hXΞ) (HasTy0.restrict hΞs (ent_and_left _ _) ht0) α hsc (ent_and_right _ _)
    have e_t' := face_all hW (.inl hXΞ) (HasTy0.restrict hΞs (ent_and_left _ _) ht'0) α hsc (ent_and_right _ _)
    have e_X := face_all hW (l := l) (.inr rfl) hXΞ α hsc (ent_and_right _ _)
    exact e_t.trans ((EqTm0.conv eΞ (EqTm0.symm e_X)).trans (EqTm0.symm e_t'))
  · have e_t := face_all hW (l := l) (.inr rfl) (HasTy0.restrict hΞs (ent_and_left _ _) ht0) α hsc (ent_and_right _ _)
    have e_t' := face_all hW (l := l) (.inr rfl) (HasTy0.restrict hΞs (ent_and_left _ _) ht'0) α hsc
      (ent_and_right _ _)
    exact e_t.trans (eΞ.trans (EqTm0.symm e_t'))

end Model.Whnf
