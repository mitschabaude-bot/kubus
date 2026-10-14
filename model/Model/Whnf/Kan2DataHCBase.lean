import Model.Whnf.Kan2DataLine
import Model.Whnf.Kan2DataFillC

/-!
# Shared utilities for composition of constructor arguments

List access, restricted argument types, and the diagonal of recursive composition, used by the
composition proof for arbitrary tube lists and its specialization to tube projections.
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

attribute [local instance] Classical.propDecidable

variable {S : Sig} {k k' : ℕ}

theorem getD_take_lt {L : List Tm} {i j : ℕ} (h : i < j) : (L.take j).getD i .abort = L.getD i .abort := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_take, h]

theorem getD_map_isub (L : List Tm) (i : ℕ) (κ : ISub k' k) :
    (L.map (·.isub κ)).getD i .abort = (L.getD i .abort).isub κ := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  rcases L[i]? with _ | a <;> rfl

/-- The argument type `i` at the restrictions of the first fillers, at the point `r`. -/
def argTyAt (d : ℕ) (D : DataDecl) (C : Ctor) (F : List Tm) (Q : Tm) {K k1 : ℕ} (ρ : ISub k1 K) (i : ℕ) {k3 : ℕ}
    (τ : ISub k3 k1) (r : I) (hr : r.Scoped k3) : Tm :=
  (C.argTy d D.params.length i).substList (((F.map (·.isub (ISub.cons r hr τ))).take i).reverse ++
    (Q.isub (ρ.comp τ)).toList.reverse)

theorem getD_eq_get {L : List Tm} {i : ℕ} (h : i < L.length) : L.getD i .abort = L[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]; rfl

theorem tele_getD {Ψ : ℕ} {Φ : I} {Γ : Ctx} {L Δ prev : List Tm} (h : HasTele0 S Ψ Φ Γ (Tm.ofList L) Δ prev)
    {j : ℕ} (hj : j < L.length) {A : Tm} (hA : Δ[j]? = some A) :
    HasTy0 S Ψ Φ Γ (L.getD j .abort) (A.substList ((L.take j).reverse ++ prev)) := by
  have := tele_get h j (L.getD j .abort) A (by rw [toList_ofList, getD_eq_get hj]; exact List.getElem?_eq_getElem hj) hA
  rwa [toList_ofList] at this

section
variable (hW : WfSig S)
include hW

/-- Compositions over a base related to itself, from those over a related pair of bases. -/
theorem HC2.self {A L L' a a' : Tm} {lL lL' : ℕ} (hAA : RT2 S k A A)
    (eLA : EqTm S k .one [] L A (.univ lL)) (eL'A : EqTm S k .one [] L' A (.univ lL'))
    (haa : RE2 S k A a a') (h : HC2 S k A L L' a a') : HC2 S k A L L a a := by
  intro φ φ' v v' hty hty' heq hteq h12 h21 htube haa0 hbd hbd'
  have hX : TyCode k (semK S k A) := RE2.tyCode hW haa
  have hAσ : ∀ {k3 : ℕ} (σ : ISub k3 k), RT2 S k3 (A.isub σ) (A.isub σ) := fun σ => RT2.isub hW hX hAA σ
  obtain ⟨l0, ⟨hL, hφs, hv, ha, hside⟩, -⟩ := gen_hcomp (spec_to_minimal hW hty) rfl
  obtain ⟨l0', ⟨-, hφs', hv', -, hside'⟩, -⟩ := gen_hcomp (spec_to_minimal hW hty') rfl
  have eLL' : TyEq S k L L' := TyEq.trans hW (.inr ⟨_, eLA⟩) (TyEq.symm (.inr ⟨_, eL'A⟩))
  obtain ⟨lm, eLL'0⟩ := tyEq_eq hW eLL' ⟨_, HasTy.eqL eL'A⟩
  have hcs : (cof .one φ).Scoped k := ⟨trivial, hφs⟩
  have hcs' : (cof .one φ').Scoped k := ⟨trivial, hφs'⟩
  have eaa : EqTm S k .one [] a a' L := (RE2.typed haa).2.2.tyConv (TyEq.symm (.inr ⟨_, eLA⟩))
  have hside1 : EqTm0 S k (cof .one φ) [] (v.dinst .zero) a' L :=
    hside.trans (EqTm0.restrict hcs (ent_and_left _ _) (spec_to_minimal_eq hW eaa))
  have ha' := spec_to_minimal hW (HasTy.eqR eaa)
  have hty1L := hcomp_retype0 hW hφs hv ha' hside1 (spec_to_minimal_eq hW eLL'0)
  have htyL : HasTy0 S k .one [] (.hcomp L φ v a) L := HasTy0.hcomp hL hφs hv ha hside
  have htyL' : HasTy0 S k .one [] (.hcomp L φ' v' a) L := HasTy0.hcomp hL hφs' hv' ha hside'
  have eA : TyEq S k L A := .inr ⟨_, eLA⟩
  have heq1 := (EqTm.hcomp (minimal_to_spec htyL) (minimal_to_spec hty1L) eLL'0 (ent_refl _) (ent_refl _)
    (EqTm.refl (minimal_to_spec hv)) eaa).tyConv eA
  have hty1 : HasTy S k .one [] (.hcomp L' φ v a') A := (minimal_to_spec hty1L).tyConv eA
  have hφ'φ : ∀ {k3 : ℕ} (σ : ISub k3 k), (ival (idEnv k3) (φ'.subst σ.τ)).holds →
      (ival (idEnv k3) (φ.subst σ.τ)).holds := fun σ hh => by
    rw [holds_iff_entails (I.scoped_subst hφs σ.sc)]
    exact ent_trans ((holds_iff_entails (I.scoped_subst hφs' σ.sc)).1 hh) (ent_subst h21 σ.τ)
  have h1 := h φ φ v v hty hty1 heq1 (EqTm.refl (HasTy.eqL hteq)) (ent_refl _) (ent_refl _)
    (fun k3 σ r r' hr hr' hE hh => RE2.trans hW (hAσ σ) (htube k3 σ r r' hr hr' hE hh)
      (RE2.symm hW (hAσ σ) (htube k3 σ r' r' hr' hr' (I_eq_refl _) hh))) haa
    (fun k3 σ hh => RE2.trans hW (hAσ σ) (hbd k3 σ hh) (RE2.isub hW haa σ))
    (fun k3 σ hh => RE2.symm hW (hAσ σ) (hbd k3 σ hh))
  have h2 := h φ' φ v' v hty' hty1 (heq.symm.trans heq1)
    (EqTm.restrict (KubusCore.I.scoped_shift hcs') (ent_shift (ent_and_mono (ent_refl _) h21)) hteq.symm) h21 h12
    (fun k3 σ r r' hr hr' hE hh => RE2.symm hW (hAσ σ) (htube k3 σ r' r hr' hr (I_eq_symm hE) (hφ'φ σ hh))) haa
    (fun k3 σ hh => RE2.trans hW (hAσ σ) (RE2.symm hW (hAσ σ) (hbd' k3 σ (hφ'φ σ hh))) (RE2.isub hW haa σ))
    (fun k3 σ hh => RE2.symm hW (hAσ σ) (hbd k3 σ (hφ'φ σ hh)))
  exact RE2.trans hW hAA h1 (RE2.symm hW hAA h2)

end

end

end Model.Whnf
