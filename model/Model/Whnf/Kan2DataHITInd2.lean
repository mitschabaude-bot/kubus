import Model.Whnf.Kan2DataHITInd

/-!
# Transport along lines of higher inductive types: contracta

The normal forms of elements of a literal higher inductive type (`WhnfF`: constructors where no boundary
holds, formal compositions whose face does not hold); the transport of an element reduces to the contractum
`tRedF` of the transport of its normal form (`tred_red`), which is a normal form, and contracta commute
with restrictions (`tRedF_isub`). Where the face of the transport holds, the contracta are related to the
normal forms (`TC.tcon_faceH`, `hcomp_faceH`).
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

attribute [local instance] Classical.propDecidable

variable {S : Sig} {k k' k'' : ℕ}

/-- The normal forms of a higher inductive type. -/
def WhnfF (d : ℕ) (D : DataDecl) (W : Tm) : Prop :=
  (∃ (c : ℕ) (C : Ctor) (q : Tm) (X : List Tm) (rs : List I), D.ctors[c]? = some C ∧
    W = .con d c q (Tm.ofList X) rs ∧ X.length = C.args.length ∧ firstBnd C.bnd rs = none) ∨
  (∃ (qs : Tm) (χ : I) (u a : Tm), W = .hcomp (.data d qs) χ u a ∧ ¬ I.Entails .one χ)

section red
variable (hW : WfSig S) {d : ℕ} {D : DataDecl} (hD : S[d]? = some (.data D)) (hp : D.params ≠ [])
  (hH : D.isHIT = true)
include hW hD hp hH

/-- The transport of an element reduces to the contractum of the transport of its normal form, a normal
form. -/
theorem tred_red {PL x W : Tm} {ψ : I} (hψ : ¬ I.Entails .one ψ) (hWF : WhnfF d D W) (hxW : RedW S x W)
    (hty : HasTy S k .one [] (.transp (.data d PL) ψ x) ((Tm.data d PL).dinst .one))
    (eW : EqTm S k .one [] x W ((Tm.data d PL).dinst .zero)) :
    Red S (.transp (.data d PL) ψ x) (tRedF d D PL ψ W) ∧
    EqTm S k .one [] (.transp (.data d PL) ψ x) (tRedF d D PL ψ W) ((Tm.data d PL).dinst .one) ∧
    IsWhnf S (tRedF d D PL ψ W) := by
  have rb := transp_rebase hW hty eW
  have r1 := red_transp_base hD hp (ps := PL) hψ hxW.1
  rcases hWF with ⟨c, C, q, X, rs, hC, rfl, hXl, hf⟩ | ⟨qs, χ, u, a, rfl, hχ⟩
  · rw [tRedF_con d D PL ψ hC]
    have hs := step_transp_conR hD hp hC (ps := PL) (qs := q) hψ hXl (step_con_none hD hC _ _ hf)
    exact ⟨r1.trans (.step hs (.refl _)), rb.2.trans (transpCon_eqR hW hD hp hC rb.1).1,
      step_con_none hD hC _ _ hf⟩
  · rw [tRedF_hcomp]
    have hs := step_transp_hcompH hD hp hH (ps := PL) (qs := qs) (u := u) (a := a) hψ hχ
    obtain ⟨_, ⟨hL, -, -, -⟩, -⟩ := gen_transpF (spec_to_minimal hW hty) rfl
    obtain ⟨D', hD', hpt⟩ := gen_data_tele hL rfl
    rw [hD] at hD'; cases hD'
    have hd0 : HasTy S k .one [] (.data d (PL.dinst .zero)) (.univ D.level) := by
      have := HasTy.isubS hW (minimal_to_spec (HasTy0.data hD (hW.2 d D hD).1 hpt)) (ISub.cons .zero trivial (ISub.id k))
      rwa [show (Tm.data d PL).isub (ISub.cons .zero trivial (ISub.id k)) = .data d (PL.isub (ISub.cons .zero trivial
        (ISub.id k))) from rfl, isub_cons_id_of_closed (by simpa [Tm.closedB] using closed_ty hL)] at this
    have hb0 := (hcomp_data_retype hW (HasTy.eqR eW) hd0).1
    exact ⟨r1.trans (.step hs (.refl _)), rb.2.trans (transpHcomp_eq hD hp hH hb0 rb.1), step_hcomp_HIT hD hH hχ⟩

end red

/-- Contracta commute with restrictions. -/
theorem tRedF_isub (hW : WfSig S) {d : ℕ} {D : DataDecl} (hD : S[d]? = some (.data D)) {PL W : Tm} {ψ : I}
    (hPl : IsList PL) (hPlen : PL.toList.length = D.params.length) (hWF : WhnfF d D W) (κ : ISub k' k) :
    (tRedF d D PL ψ W).isub κ = tRedF d D (PL.isub κ.up) (ψ.subst κ.τ) (W.isub κ) := by
  rcases hWF with ⟨c, C, q, X, rs, hC, rfl, hXl, -⟩ | ⟨qs, χ, u, a, rfl, -⟩
  · rw [tRedF_con d D PL ψ hC, isub_conT, tRedF_con d D _ _ hC, tConR_isub hW hD hC hPl hPlen hXl κ]
  · rw [tRedF_hcomp, tHc_isub]
    rfl

namespace TC

variable {d : ℕ} {D : DataDecl} {PL : Tm} {φ : I} {c : ℕ} {C : Ctor} {q : Tm} {X : List Tm} {rs : List I}

/-- Where the face of a transport of a constructor holds, its `transpCon` contractum is related to the
constructor. -/
theorem tcon_faceH (H : TC S k d D PL PL φ φ c C q q X X rs rs) (hH : D.isHIT = true) (hyp : HITHyp2 S)
    (hφ : I.Entails .one φ) :
    RE2 S k (.data d (PL.dinst .one)) (tConR d D c C PL φ X rs) (.con d c q (Tm.ofList X) rs) := by
  have hW := H.hW
  obtain ⟨-, -, -, -, -, -, hPl, -, -, -, hPc, -⟩ := H.basic
  obtain ⟨hd1, s1, -, -, hc1⟩ := H.end_data
  have hP0 : PL.isub (ISub.cons .zero trivial (ISub.id k)) = PL.dinst .zero := isub_cons_id_of_closed hPc .zero trivial
  have hP1 : PL.isub (ISub.cons .one trivial (ISub.id k)) = PL.dinst .one := isub_cons_id_of_closed hPc .one trivial
  have hholds : (ival (idEnv k) (φ.subst (ISub.id k).τ)).holds := by
    rw [I_subst_id H.hφs]; exact (holds_iff_entails H.hφs).2 hφ
  have h10 := H.hLC k (ISub.id k) .one trivial hholds
  rw [show (Tm.data d PL).isub (ISub.cons .one trivial (ISub.id k)) = .data d (PL.dinst .one) by
      show Tm.data d (PL.isub _) = _; rw [hP1],
    show (Tm.data d PL).isub (ISub.cons .zero trivial (ISub.id k)) = .data d (PL.dinst .zero) by
      show Tm.data d (PL.isub _) = _; rw [hP0]] at h10
  have FA := H.face_args hφ
  obtain ⟨-, ⟨-, -, -, hb0⟩, -⟩ := gen_transpF (spec_to_minimal hW H.hty) rfl
  have hcb : HasTy S k .one [] (.con d c q (Tm.ofList X) rs) (.data d (PL.dinst .one)) :=
    (minimal_to_spec hb0 : HasTy S k .one [] _ (.data d (PL.dinst .zero))).tyConv (TyEq.symm (Comp2_ty_base h10).2.2.2.2.2)
  obtain ⟨eT, -⟩ := H.basic
  have R := con_rel hW H.hD hd1 s1 hH hyp c (ISub.id k) H.hC
    (by rw [isub_id_of_closed hc1]; exact (HasTy.eqR eT : HasTy S k .one [] (.con d c (PL.dinst .one)
      (Tm.ofList (tOuts d D C PL φ X)) rs) _))
    (by rw [isub_id_of_closed hc1]; exact hcb) (forall2_ieq_refl _) (fun i hi => by
      rw [isub_id_of_closed hc1]
      obtain ⟨T, R⟩ := FA i hi
      exact RE2.conv hW T (RE2.symm hW T R))
  rw [isub_id_of_closed hc1] at R
  exact R

end TC

end

end Model.Whnf
