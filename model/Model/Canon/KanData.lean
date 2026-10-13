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
