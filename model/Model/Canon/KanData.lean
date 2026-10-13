import Model.Canon.KanDerived
import Model.Canon.ArgConv
import Model.Canon.KanPath
import Model.Canon.DataKripke

/-!
# Canonicity: the Kan operations at inductive types
-/

set_option autoImplicit false

namespace Model.Canon

open KubusCore KubusCore.Meta

noncomputable section

variable {S : Sig} {k k' m : ℕ}

variable (hW : WfSig S)
include hW

theorem dataMem_of_ty {Θ : SData m} {f : Hom k m} {T t : Tm} (hsem : semK S k T = res f (dataC Θ))
    (ht : HasTy S k .one [] t T) : dataMem S Θ f k (Hom.id k) t := by
  have := mem_of_ty hW ht
  rw [hsem, El_res, Hom.comp_id, El_dataC] at this
  unfold dataMem
  rw [Hom.comp_id, delemSet_restr, Hom.comp_id]; exact this

theorem kanH_data {Θ : SData m} (hKR : KR S m (dataC Θ)) {f : Hom k m} {T : Tm}
    (hT : (Comp S (dataC Θ) m k f).ty T) : KanH S k T := by
  intro φ u a hty hu ha
  obtain ⟨-, ⟨-, hφ, -, -, -⟩, -⟩ := gen_hcomp (Φ := .one) (Γ := []) (spec_to_minimal hW hty) rfl
  by_cases hh : (ival (idEnv k) φ).holds
  · exact RE_hcomp_face hW hty hu hh
  have hT' := hT
  rw [Comp_dataC] at hT'
  obtain ⟨⟨hTy, hsem⟩, ps, hE, hpl, -⟩ := hT'
  unfold RE at ha ⊢
  rw [← Comp_eq_semK hT] at ha ⊢
  rw [Comp_dataC] at ha ⊢
  obtain ⟨hat, -, -, hadr⟩ := ha
  have hMem : ∀ k1 (f1 : Hom k1 k) t t' A, EqTm S k1 .one [] t t' A → dataMem S Θ f k1 f1 t → dataMem S Θ f k1 f1 t' :=
    fun k1 f1 t t' A e hm => by unfold dataMem at hm ⊢; rwa [← semK_eq hW e]
  have hmem : semK S k (.hcomp T φ u a) ∈ El (res f (dataC Θ)) (Hom.id k) := by
    rw [← hsem]; exact mem_of_ty hW hty
  cases hH : (dataD S Θ.idx).isHIT
  · sorry
  · refine ⟨hty, hmem, hty, DR.hcomp (u := u) (a := a) (dataMem_of_ty hW hsem hty) hH hφ hh hpl hE ?_
      (DR.conv hW hMem hadr hE (EqTm.refl (hat.tyConv hE))) (fun k' σ r hr hh' => ?_)⟩
    · rcases hE with rfl | ⟨l, e⟩
      · exact EqTm.refl hty
      · exact (hcomp_retype hW hty e).2
    · have h1 := hu k' σ r hr hh'
      have hTσ := (hKR k f k' σ T T).1 hT
      unfold RE at h1
      rw [← Comp_eq_semK hTσ, Comp_dataC] at h1
      obtain ⟨h1t, -, -, h1dr⟩ := h1
      have h2 := DR.unbase f h1dr
      rw [Hom.comp_id] at h2
      rw [Hom.id_comp]
      exact DR.conv hW hMem h2 (hE.isub hW σ) (EqTm.refl (h1t.tyConv (hE.isub hW σ)))

/-- A computable element of an inductive type, from its relation. -/
theorem RE_of_DR {Θ : SData m} {k0 : ℕ} {f : Hom k0 m} {k' : ℕ} {g : Hom k' k0} {A t : Tm}
    (hty : (Comp S (dataC Θ) m k' (f.comp g)).ty A)
    (hr : DR S Θ.idx (dataD S Θ.idx) (dataMem S Θ f) (dataP S Θ f) k' g A t) : RE S k' A t := by
  unfold RE; rw [← Comp_eq_semK hty, Comp_dataC]
  refine ⟨hr.typed, ?_, hr.typed, DR.rebase f hr g (Hom.id k') (Hom.comp_id _).symm⟩
  have := hr.mem
  unfold dataMem at this
  rw [res_dataC, El_dataC, delemSet_restr, Hom.comp_id]
  rw [delemSet_restr, Hom.comp_id] at this; exact this

/-- The relation of a computable element of an inductive type. -/
theorem DR_of_RE {Θ : SData m} {k0 : ℕ} {f : Hom k0 m} {k' : ℕ} {g : Hom k' k0} {A t : Tm}
    (hty : (Comp S (dataC Θ) m k' (f.comp g)).ty A) (ht : RE S k' A t) :
    DR S Θ.idx (dataD S Θ.idx) (dataMem S Θ f) (dataP S Θ f) k' g A t := by
  unfold RE at ht; rw [← Comp_eq_semK hty, Comp_dataC] at ht
  have := DR.unbase f ht.2.2.2
  rwa [Hom.comp_id] at this

omit hW in
theorem skip_isub {τ : ℕ → I} (h0 : τ 0 = .var 0) (h1 : ∀ n, τ (n + 1) = .var (n + 2)) (X u : Tm) (ψ : I)
    {k'' : ℕ} (r : I) (hr : r.Scoped k'') (σ : ISub k'' k') :
    (Tm.transp (X.dsubst τ) ψ.shift u).isub (ISub.cons r hr σ) =
      .transp (X.isub σ.up) (ψ.subst σ.τ) (u.isub (ISub.cons r hr σ)) := by
  show Tm.transp ((X.dsubst τ).subst .var (ISub.cons r hr σ).up.τ) (ψ.shift.subst (ISub.cons r hr σ).τ)
    (u.isub (ISub.cons r hr σ)) = _
  rw [I_shift_cons]
  congr 1
  simp only [Tm.dsubst, Tm.isub, subst_subst]
  refine subst_congr (fun _ => rfl) (fun i => ?_) X
  rcases i with _ | i
  · rw [h0]; rfl
  · rw [h1]; rfl

omit hW in
theorem cons0_comp {k'' : ℕ} (σ : ISub k'' k') :
    (ISub.cons .zero trivial (ISub.id k')).comp σ = σ.up.comp (ISub.cons .zero trivial (ISub.id k'')) := by
  ext i
  rcases i with _ | i
  · rfl
  · show ((ISub.id k').τ i).subst σ.τ = ((σ.τ i).shift).subst (ISub.cons .zero trivial (ISub.id k'')).τ
    rw [I_shift_cons]
    by_cases h : i < k'
    · simp only [ISub.id, if_pos h]
      exact (ISub.I.subst_scoped_id (σ.sc i h) fun j hj => by simp [ISub.id, hj]).symm
    · simp only [ISub.id, if_neg h]; rw [σ.hi i (by omega)]; rfl

end

end Model.Canon
