import Model.Whnf.Kan2DataHITLine

/-!
# Transport of boundary terms of higher inductive types: instances and nested argument lines

`BI c C rs a`: at every instance of the constructor `c` (parameters, arguments related to themselves and a
restriction of the interval arguments `rs`, where a boundary holds), the relations of the argument types of
the nested constructors of the subterm `a` of the boundary (`bndRel`), and the typing of `a`. It holds for
the boundaries that hold (`BI_top`) and passes to the recursive arguments of nested constructors (`BI_sub`).
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

attribute [local instance] Classical.propDecidable

variable {S : Sig} {k k' k'' : ℕ}

/-- A nested constructor of a simple boundary. -/
theorem simpleB_con_inv {ctors : List Ctor} {d np c n : ℕ} {C : Ctor} {d' c' : ℕ} {ps0 as0 : Tm} {rs0 : List I}
    (h : Ctor.simpleB ctors d np c n C (.con d' c' ps0 as0 rs0) = true) :
    d' = d ∧ c' < c ∧ ps0 = Ctor.paramVars np n ∧ ∃ C', ctors[c']? = some C' ∧ as0.toList.length = C'.args.length ∧
      rs0.length = C'.dims ∧ Ctor.simpleArgs ctors d np c n C C' 0 as0 = true ∧ as0 = Tm.ofList as0.toList := by
  simp only [Ctor.simpleB, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hdd, hcc⟩, hps⟩, hm⟩ := h
  refine ⟨hdd, hcc, hps, ?_⟩
  cases hC' : ctors[c']? with
  | none => rw [hC'] at hm; cases hm
  | some C' =>
    rw [hC'] at hm
    simp only [Bool.and_eq_true, beq_iff_eq] at hm
    obtain ⟨⟨hal, hrl⟩, hsa⟩ := hm
    exact ⟨C', rfl, hal, hrl, hsa, simpleArgs_isList as0 0 hsa⟩

/-- The instances of a subterm `a` of a boundary of constructor `c` (at interval arguments `rs`). -/
def BI (S : Sig) (d : ℕ) (D : DataDecl) (c : ℕ) (C : Ctor) (rs : List I) (a : Tm) : Prop :=
  ∀ {k3 : ℕ} (P1 : Tm) (Y : List Tm) (τ : ℕ → I), HasTy S k3 .one [] (.data d P1) (.univ D.level) →
    RT2 S k3 (.data d P1) (.data d P1) → Y.length = C.args.length →
    HasTy S k3 .one [] (.con d c P1 (Tm.ofList Y) (rs.map (·.subst τ))) (.data d P1) →
    (∀ i (hi : i < C.args.length), RE2 S k3 ((C.argTy d D.params.length i).substList
      ((Y.take i).reverse ++ P1.toList.reverse)) (Y.getD i .abort) (Y.getD i .abort)) →
    bndRel S k3 d D.params.length C.args.length C D.ctors P1 P1 Y Y (rs.map (·.subst τ)) a ∧
    HasTy S k3 .one [] (Ctor.bndAt a P1.toList Y (rs.map (·.subst τ))) (.data d P1)

section bi
variable (hW : WfSig S) {d : ℕ} {D : DataDecl} (hD : S[d]? = some (.data D))
include hW hD

/-- The boundaries that hold. -/
theorem BI_top (hH : D.isHIT = true) (hyp : HITHyp2 S) {c : ℕ} {C : Ctor} (hC : D.ctors[c]? = some C)
    {rs : List I} (hrsl : rs.length = C.dims) {kb : ℕ} {ψ : I} {b : Tm} (hb : C.bnd[kb]? = some (ψ, b))
    (hent : I.Entails .one (Ctor.cofAt ψ rs)) : BI S d D c C rs b := by
  intro k3 P1 Y τ hP1 hPP hYl hcT hY
  obtain ⟨hψs, -⟩ := ((hW.2 d D hD).2.2 c C hC).2.1 kb ψ b hb
  have hent' : I.Entails .one (Ctor.cofAt ψ (rs.map (·.subst τ))) := by
    rw [← cofAt_subst τ (by rw [hrsl]; exact hψs)]; exact ent_one_subst hent τ
  have hPl := (con_inv hW hD hC hcT hP1).2.2.1
  refine ⟨hyp.bndTy hD hH hC hb hent' hP1 hPP hYl hYl hcT hY, ?_⟩
  have := EqTm.conBnd hD hC hb hent' hPl (by rw [toList_ofList]) hcT
  rw [toList_ofList] at this
  exact HasTy.eqR this

/-- The recursive arguments of a nested constructor. -/
theorem BI_sub {c : ℕ} {C : Ctor} (hC : D.ctors[c]? = some C) {rs : List I} {c' : ℕ} {ps0 as0 : Tm} {rs0 : List I}
    (hs : Ctor.simpleB D.ctors d D.params.length c C.args.length C (.con d c' ps0 as0 rs0) = true)
    (h : BI S d D c C rs (.con d c' ps0 as0 rs0)) {C' : Ctor} (hC' : D.ctors[c']? = some C') {j : ℕ}
    (hj : j < as0.toList.length) (hr : C'.isRec j = true) : BI S d D c C rs as0.toList[j] := by
  obtain ⟨-, -, rfl, C1, hC1, hal, -, hsa, hasL⟩ := simpleB_con_inv hs
  rw [hC'] at hC1; cases hC1
  intro k3 P1 Y τ hP1 hPP hYl hcT hY
  obtain ⟨hrel, hty⟩ := h P1 Y τ hP1 hPP hYl hcT hY
  simp only [bndRel, hC'] at hrel
  refine ⟨(bndRelArgs_get as0 0 [] hrel j hj).2 (by simpa using hr), ?_⟩
  have hPl := (con_inv hW hD hC (C := C) hcT hP1).2.2.1
  have hplen : P1.toList.length = D.params.length := by
    have := data_len_of hW (⟨_, .inl hP1⟩ : IsTyK S k3 (.data d P1)); rwa [dataD_eq hW hD] at this
  rw [bndAt_con, bndAt_paramVars _ hplen hYl, show Ctor.bndAt as0 P1.toList Y (rs.map (·.subst τ)) =
    Tm.ofList (as0.toList.map (Ctor.bndAt · P1.toList Y (rs.map (·.subst τ)))) from by
      conv_lhs => rw [hasL]
      exact bndAt_ofList _ _ _ _, ← hPl] at hty
  obtain ⟨htele, -⟩ := con_inv hW hD hC' hty hP1
  have hi : j < C'.args.length := by omega
  have g := HasTele0.get htele (k := j) (a := Ctor.bndAt as0.toList[j] P1.toList Y (rs.map (·.subst τ)))
    (by rw [toList_ofList, List.getElem?_map, List.getElem?_eq_getElem hj]; rfl) (argTys_get hi)
  rw [argTy_rec_inst hr hPl hplen (by simp [toList_ofList]; omega)] at g
  exact minimal_to_spec g

end bi

theorem shift_map_subst (rs : List I) {k3 : ℕ} (σ : ISub k3 (k + 1)) :
    (rs.map (·.shift)).map (·.subst σ.τ) = rs.map (·.subst σ.tail.τ) := by
  rw [List.map_map]; congr 1; funext r
  show (r.shift).subst σ.τ = r.subst σ.tail.τ
  simp only [I.shift, I_ren_subst]; rfl

namespace TC

variable {d : ℕ} {D : DataDecl} {PL QL : Tm} {φ φ' : I} {c : ℕ} {C : Ctor} {q q' : Tm} {X X' : List Tm}
  {rs rs' : List I} (H : TC S k d D PL QL φ φ' c C q q' X X' rs rs')
include H

/-- The interval arguments are scoped. -/
theorem rs_scoped : ∀ r ∈ rs, r.Scoped k := by
  have hW := H.hW
  obtain ⟨-, ⟨-, -, -, hb⟩, -⟩ := gen_transpF (spec_to_minimal hW H.hty) rfl
  obtain ⟨⟨-, -, -, -, -, -, -, -, -, -, hsc⟩, -⟩ := gen_conF hb rfl
  exact hsc

/-- The constructor of the fillers, at a point of the line: typed, with arguments related to themselves. -/
theorem fill_inst {k3 : ℕ} (σ : ISub k3 (k + 1)) :
    HasTy S k3 .one [] (.con d c (PL.isub σ) (Tm.ofList ((tF d D C PL φ X).map (·.isub σ))) (rs.map (·.subst σ.tail.τ)))
      (.data d (PL.isub σ)) ∧
    ∀ i (hi : i < C.args.length), RE2 S k3 ((C.argTy d D.params.length i).substList
      ((((tF d D C PL φ X).map (·.isub σ)).take i).reverse ++ (PL.isub σ).toList.reverse))
      (((tF d D C PL φ X).map (·.isub σ)).getD i .abort) (((tF d D C PL φ X).map (·.isub σ)).getD i .abort) := by
  have hW := H.hW
  obtain ⟨-, -, -, -, hXl, -, hPl, -, hPlen, -, -, -⟩ := H.basic
  have hlF := tF_length d D C PL φ X
  obtain ⟨D2, hD2, hpt⟩ := gen_data_tele (spec_to_minimal hW H.hPL) rfl
  rw [H.hD] at hD2; cases hD2
  have hrsl : rs.length = C.dims := by
    obtain ⟨-, ⟨-, -, -, hb⟩, -⟩ := gen_transpF (spec_to_minimal hW H.hty) rfl
    obtain ⟨⟨-, D0, C0, hD0, hC0, -, -, -, -, hr, -⟩, -⟩ := gen_conF hb rfl
    rw [H.hD] at hD0; cases hD0; rw [H.hC] at hC0; cases hC0; exact hr
  have htele : HasTele0 S (k + 1) .one [] (Tm.ofList (tF d D C PL φ X)) (C.argTys d D.params.length)
      PL.toList.reverse := by
    refine HasTele0.ofList_of (wf_of_ty (spec_to_minimal hW H.hPL)) _ _ _ (by simp [argTys_length, hlF])
      fun j a A ha hA => ?_
    have hj : j < C.args.length := by obtain ⟨h1, -⟩ := List.getElem?_eq_some_iff.1 ha; omega
    rw [argTys_get hj] at hA; cases hA
    obtain ⟨-, -, -, htyF, -, -⟩ := tcon_typing hW H.hD H.hp H.hC H.hty hj
    have ea : a = (tF d D C PL φ X).getD j .abort := by
      rw [List.getD_eq_getElem?_getD, ha]; rfl
    rw [ea, tF_getD d D C PL φ X hj, ← tl_eq d D C PL φ X hj.le]
    exact spec_to_minimal hW htyF
  have hc : HasTy0 S (k + 1) .one [] (.con d c PL (Tm.ofList (tF d D C PL φ X)) (rs.map (·.shift))) (.data d PL) :=
    HasTy0.con H.hD H.hC hPl (spec_to_minimal hW H.hPL) hpt htele (by simp [hrsl])
      (fun r hr => by
        obtain ⟨r0, hr0, rfl⟩ := List.mem_map.1 hr
        exact KubusCore.I.scoped_shift (H.rs_scoped r0 hr0))
  have h1 := HasTy.isubS hW (minimal_to_spec hc) σ
  rw [isub_conT, shift_map_subst] at h1
  refine ⟨h1, fun i hi => ?_⟩
  have G := H.fill_self (H.good_all i hi) σ.tail (σ.τ 0) (σ.τ 0) (σ.sc 0 (by omega)) (σ.sc 0 (by omega)) (I_eq_refl _)
  rw [ISub.cons_tail] at G
  rw [tl_isub hW H.hD H.hC hPl φ X hi.le] at G
  rw [getD_map_isub' (by omega), tF_getD d D C PL φ X hi]
  exact G

end TC

end

end Model.Whnf
