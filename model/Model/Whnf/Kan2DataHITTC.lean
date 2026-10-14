import Model.Whnf.Kan2DataTInd
import Model.Whnf.Kan2DataHITConRel

/-!
# Transport of constructors of higher inductive types: the data `TC`

At a higher inductive type, the field `TC.conR` (constructors with related arguments at the end of the
lines are related) follows from `con_rel`. The data `TC` restricts along lines (`TC.restrLine`): to the
lines `y ↦ P(y(z), τ)` of a restriction `τ`, for any `y` starting at `0`.
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

attribute [local instance] Classical.propDecidable

variable {S : Sig} {k k' k'' : ℕ}

section hit
variable (hW : WfSig S) {d : ℕ} {D : DataDecl} (hD : S[d]? = some (.data D)) (hH : D.isHIT = true)
  (hyp : HITHyp2 S)
include hW hD hH hyp

/-- The field `TC.conR` at a higher inductive type. -/
theorem conR_hit {PL QL : Tm} {c : ℕ} {C : Ctor} {rs rs' : List I} (hC : D.ctors[c]? = some C)
    (hPL : HasTy S (k + 1) .one [] (.data d PL) (.univ D.level))
    (hRL : ∀ k3 (τ : ISub k3 k) (y y' : I) (hy : y.Scoped k3) (hy' : y'.Scoped k3), I.Eq y y' →
      RT2 S k3 (.data d (PL.isub (ISub.cons y hy τ))) (.data d (PL.isub (ISub.cons y' hy' τ))))
    (hrs : List.Forall₂ I.Eq rs rs') :
    ∀ (Y Y' : List Tm), Y.length = C.args.length → Y'.length = C.args.length →
    HasTy S k .one [] (.con d c (PL.dinst .one) (Tm.ofList Y) rs) (.data d (PL.dinst .one)) →
    EqTm S k .one [] (.con d c (PL.dinst .one) (Tm.ofList Y) rs) (.con d c (QL.dinst .one) (Tm.ofList Y') rs')
      (.data d (PL.dinst .one)) →
    (∀ i (hi : i < C.args.length), RE2 S k ((C.argTy d D.params.length i).substList
      ((Y.take i).reverse ++ (PL.dinst .one).toList.reverse)) (Y.getD i .abort) (Y'.getD i .abort)) →
    RE2 S k (.data d (PL.dinst .one)) (.con d c (PL.dinst .one) (Tm.ofList Y) rs)
      (.con d c (QL.dinst .one) (Tm.ofList Y') rs') := by
  intro Y Y' _ _ hcT he hargs
  have hPc : PL.closedB 0 (k + 1) = true := data_closed hW hD hPL
  have hP1 : PL.isub (ISub.cons .one trivial (ISub.id k)) = PL.dinst .one := isub_cons_id_of_closed hPc .one trivial
  have hd1 : HasTy S k .one [] (.data d (PL.dinst .one)) (.univ D.level) := by
    have := HasTy.isubS hW hPL (ISub.cons .one trivial (ISub.id k)); rwa [show (Tm.data d PL).isub
      (ISub.cons .one trivial (ISub.id k)) = .data d (PL.isub (ISub.cons .one trivial (ISub.id k))) from rfl, hP1] at this
  have s1 := hRL k (ISub.id k) .one .one trivial trivial (I_eq_refl _)
  rw [hP1] at s1
  have hc1 : (PL.dinst .one).closedB 0 k = true := data_closed hW hD hd1
  have := con_rel hW hD hd1 s1 hH hyp c (ISub.id k) hC (by rw [isub_id_of_closed hc1]; exact hcT)
    (by rw [isub_id_of_closed hc1]; exact HasTy.eqR he) hrs (fun i hi => by rw [isub_id_of_closed hc1]; exact hargs i hi)
  rwa [isub_id_of_closed hc1] at this

end hit

namespace TC

variable {d : ℕ} {D : DataDecl} {PL QL : Tm} {φ φ' : I} {c : ℕ} {C : Ctor} {q q' : Tm} {X X' : List Tm}
  {rs rs' : List I} (H : TC S k d D PL QL φ φ' c C q q' X X' rs rs')
include H

omit H in
/-- The start of a line, at a restriction. -/
theorem start_isub {k3 : ℕ} (τ : ISub k3 k) : (PL.dinst .zero).isub τ = PL.isub (ISub.cons .zero trivial τ) := by
  rw [isub_dinst]; exact isub_up_dinst PL τ .zero trivial

/-- A point of a restricted line, as a restriction of the line. -/
theorem line_pt {k3 : ℕ} (τ : ISub k3 k) (y : I) (hy : y.Scoped (k3 + 1)) (r : I) (hr : r.Scoped k3) :
    (PL.isub (ISub.cons y hy τ.up.tail)).dinst r =
      PL.isub (ISub.cons (y.subst (ISub.cons r hr (ISub.id k3)).τ) (I.scoped_subst hy (ISub.cons r hr (ISub.id k3)).sc) τ) := by
  have hc : (PL.isub (ISub.cons y hy τ.up.tail)).closedB 0 (k3 + 1) = true :=
    data_closed H.hW H.hD (HasTy.isubS H.hW H.hPL (ISub.cons y hy τ.up.tail))
  rw [← isub_cons_id_of_closed hc r hr, Tm.isub_isub, line_comp, ISub.comp_id]

/-- The arguments are related to themselves. -/
theorem args0_self : ∀ i (hi : i < C.args.length), RE2 S k ((C.argTy d D.params.length i).substList
    ((X.take i).reverse ++ (PL.dinst .zero).toList.reverse)) (X.getD i .abort) (X.getD i .abort) := by
  have hW := H.hW
  obtain ⟨-, -, -, -, hXl, hX'l, hPl, -, -, -, hPc, -⟩ := H.basic
  have hP0 : PL.isub (ISub.cons .zero trivial (ISub.id k)) = PL.dinst .zero := isub_cons_id_of_closed hPc .zero trivial
  have hd0 : HasTy S k .one [] (.data d (PL.dinst .zero)) (.univ D.level) := by
    have := HasTy.isubS hW H.hPL (ISub.cons .zero trivial (ISub.id k)); rwa [show (Tm.data d PL).isub
      (ISub.cons .zero trivial (ISub.id k)) = .data d (PL.isub (ISub.cons .zero trivial (ISub.id k))) from rfl, hP0] at this
  have s0 := H.hRL k (ISub.id k) .zero .zero trivial trivial (I_eq_refl _)
  rw [hP0] at s0
  have hc0 : (PL.dinst .zero).closedB 0 k = true := data_closed hW H.hD hd0
  intro i hi
  have := (args_self hW H.hD hd0 s0 (ISub.id k) H.hC hXl hX'l (fun j hj => by
    rw [isub_id_of_closed hc0]; exact H.hargs0 j hj) i hi).2.1
  rwa [isub_id_of_closed hc0] at this

/-- The data restricted along lines: to the lines `y ↦ P(y(z), τ)`, `y ↦ Q(y'(z), τ)` of a restriction `τ`,
for `I.Eq`-equal `y`, `y'` starting at `0`, with new faces. -/
theorem restrLine (hH : D.isHIT = true) (hyp : HITHyp2 S) (hrs : List.Forall₂ I.Eq rs rs') {k3 : ℕ} (τ : ISub k3 k)
    (y y' : I) (hy : y.Scoped (k3 + 1)) (hy' : y'.Scoped (k3 + 1)) (hE : I.Eq y y')
    (h0 : I.Eq (y.subst (ISub.cons .zero trivial (ISub.id k3)).τ) .zero) {ψ ψ' : I} (hψs : ψ.Scoped k3)
    (h12 : I.Entails ψ ψ') (h21 : I.Entails ψ' ψ)
    (hLC : LineConst S k3 (.data d (PL.isub (ISub.cons y hy τ.up.tail))) ψ)
    (hty : HasTy S k3 .one [] (.transp (.data d (PL.isub (ISub.cons y hy τ.up.tail))) ψ
      (.con d c (q.isub τ) (Tm.ofList (X.map (·.isub τ))) (rs.map (·.subst τ.τ))))
      (.data d ((PL.isub (ISub.cons y hy τ.up.tail)).dinst .one)))
    (hty' : HasTy S k3 .one [] (.transp (.data d (QL.isub (ISub.cons y' hy' τ.up.tail))) ψ'
      (.con d c (q'.isub τ) (Tm.ofList (X'.map (·.isub τ))) (rs'.map (·.subst τ.τ))))
      (.data d ((PL.isub (ISub.cons y hy τ.up.tail)).dinst .one)))
    (heq : EqTm S k3 .one [] (.transp (.data d (PL.isub (ISub.cons y hy τ.up.tail))) ψ
      (.con d c (q.isub τ) (Tm.ofList (X.map (·.isub τ))) (rs.map (·.subst τ.τ))))
      (.transp (.data d (QL.isub (ISub.cons y' hy' τ.up.tail))) ψ'
      (.con d c (q'.isub τ) (Tm.ofList (X'.map (·.isub τ))) (rs'.map (·.subst τ.τ))))
      (.data d ((PL.isub (ISub.cons y hy τ.up.tail)).dinst .one))) :
    TC S k3 d D (PL.isub (ISub.cons y hy τ.up.tail)) (QL.isub (ISub.cons y' hy' τ.up.tail)) ψ ψ' c C (q.isub τ)
      (q'.isub τ) (X.map (·.isub τ)) (X'.map (·.isub τ)) (rs.map (·.subst τ.τ)) (rs'.map (·.subst τ.τ)) := by
  have hW := H.hW
  have hS := sigClosed_of_wfSig hW
  obtain ⟨-, -, -, -, hXl, hX'l, hPl, -, hPlen, -, hPc, -⟩ := H.basic
  have hPL' : HasTy S (k3 + 1) .one [] (.data d (PL.isub (ISub.cons y hy τ.up.tail))) (.univ D.level) :=
    HasTy.isubS hW H.hPL _
  have hRL' := Rob.line H.hRL τ y y hy hy (I_eq_refl _)
  -- the arguments at the start of the restricted line
  have hPl0 : IsList (PL.dinst .zero) := isList_subst hPl _ _
  have hd0τ : HasTy S k3 .one [] (.data d (PL.isub (ISub.cons .zero trivial τ))) (.univ D.level) :=
    HasTy.isubS hW H.hPL _
  have s0τ := H.hRL k3 τ .zero .zero trivial trivial (I_eq_refl _)
  have hy0 := I.scoped_subst hy (ISub.cons .zero trivial (ISub.id k3)).sc
  have r0 := H.hRL k3 τ .zero _ trivial hy0 (I_eq_symm h0)
  have hself0 := H.args0_self
  have hargs0' : ∀ i (hi : i < C.args.length), RE2 S k3 ((C.argTy d D.params.length i).substList
      (((X.map (·.isub τ)).take i).reverse ++ ((PL.isub (ISub.cons y hy τ.up.tail)).dinst .zero).toList.reverse))
      ((X.map (·.isub τ)).getD i .abort) ((X'.map (·.isub τ)).getD i .abort) := by
    intro i hi
    have restr : ∀ {Z : List Tm}, Z.length = C.args.length → ∀ {j : ℕ} (hj : j < C.args.length),
        RE2 S k ((C.argTy d D.params.length j).substList ((X.take j).reverse ++ (PL.dinst .zero).toList.reverse))
          (X.getD j .abort) (Z.getD j .abort) →
        RE2 S k3 ((C.argTy d D.params.length j).substList (((X.map (·.isub τ)).take j).reverse ++
          (PL.isub (ISub.cons .zero trivial τ)).toList.reverse)) ((X.map (·.isub τ)).getD j .abort)
          ((Z.map (·.isub τ)).getD j .abort) := by
      intro Z hZl j hj h
      have := RE2.isub hW h τ
      rw [argTy_isub hS H.hD H.hC j X hPl0 τ, start_isub] at this
      rwa [getD_map_isub' (by omega) τ, getD_map_isub' (by omega) τ]
    have T := argTy_rt2' hW H.hD hd0τ s0τ r0 H.hC hi (A := (X.map (·.isub τ)).take i) (B := (X.map (·.isub τ)).take i)
      (by simp; omega) (by simp; omega) (fun l hl => by
        rw [List.take_take, Nat.min_eq_left hl.le, getD_take_lt hl]
        exact restr hXl (by omega) (hself0 l (by omega)))
    rw [H.line_pt τ y hy .zero trivial]
    exact RE2.conv hW T (restr hX'l hi (H.hargs0 i hi))
  refine ⟨hW, H.hD, H.hp, H.hC, hPL', Rob.line H.hR τ y y' hy hy' hE, hRL', argK_restr H.hArgK _, hψs, h12, h21,
    hLC, hty, hty', heq, hargs0', ?_, conR_hit hW H.hD hH hyp H.hC hPL' hRL' (forall2_ieq_map hrs τ.τ)⟩
  intro i hi hri k4 τ2 z z' hz hz' hEz hz0
  have h := H.hrecT i hi hri k4 (τ.comp τ2) _ _ (I.scoped_subst hy (ISub.cons z hz τ2.up.tail).sc)
    (I.scoped_subst hy' (ISub.cons z' hz' τ2.up.tail).sc) (ieq_subst_cons hE hEz hz hz' τ2.up.tail)
    (ieq_zero_comp hy h0 hz hz0 τ2)
  rw [getD_map_isub' (by omega), getD_map_isub' (by omega), Tm.isub_isub, Tm.isub_isub]
  show KanT2At S k4 (Tm.data d ((PL.isub _).isub _)) (Tm.data d ((QL.isub _).isub _)) _ _
  rw [Tm.isub_isub, Tm.isub_isub, line_comp, line_comp, ISub.comp_up_tail]
  exact h

/-- The data, restricted. -/
theorem isubH (hH : D.isHIT = true) (hyp : HITHyp2 S) (hrs : List.Forall₂ I.Eq rs rs') {k4 : ℕ} (σ : ISub k4 k) :
    TC S k4 d D (PL.isub σ.up) (QL.isub σ.up) (φ.subst σ.τ) (φ'.subst σ.τ) c C (q.isub σ) (q'.isub σ)
      (X.map (·.isub σ)) (X'.map (·.isub σ)) (rs.map (·.subst σ.τ)) (rs'.map (·.subst σ.τ)) := by
  have hW := H.hW
  have e := ISub.cons_var0_up_tail σ
  have eT : ∀ (L : Tm) (ψ : I) (q0 : Tm) (Z : List Tm) (rZ : List I),
      (Tm.transp (.data d L) ψ (.con d c q0 (Tm.ofList Z) rZ)).isub σ =
        .transp (.data d (L.isub σ.up)) (ψ.subst σ.τ) (.con d c (q0.isub σ) (Tm.ofList (Z.map (·.isub σ)))
          (rZ.map (·.subst σ.τ))) := by
    intro L ψ q0 Z rZ
    show Tm.transp (Tm.data d (L.isub σ.up)) (ψ.subst σ.τ) ((Tm.con d c q0 (Tm.ofList Z) rZ).isub σ) = _
    rw [isub_conT]
  have e1 : (Tm.data d (PL.dinst .one)).isub σ = .data d ((PL.isub σ.up).dinst .one) := by
    show Tm.data d ((PL.dinst .one).isub σ) = _; rw [isub_dinst]; rfl
  have hty := HasTy.isubS hW H.hty σ
  have hty' := HasTy.isubS hW H.hty' σ
  have heq := EqTm.isubS hW H.heq σ
  rw [eT, e1] at hty
  rw [eT, e1] at hty'
  rw [eT, eT, e1] at heq
  have h := H.restrLine hH hyp hrs σ (.var 0) (.var 0) (show 0 < k4 + 1 by omega) (show 0 < k4 + 1 by omega)
    (I_eq_refl _) (I_eq_refl _) (I.scoped_subst H.hφs σ.sc) (ent_subst H.h12 _) (ent_subst H.h21 _)
    (by rw [e]; exact LineConst.isub H.hLC σ) (by rw [e]; exact hty) (by rw [e]; exact hty') (by rw [e]; exact heq)
  rw [e] at h
  exact h

end TC

end

end Model.Whnf
